#!/usr/bin/env python3
"""
IkaTracker -> Discord: alerts for NEW inactive players on Nereus (s70-en).

Watches https://ikatracker.com/atlas/recent_inactives for one server and posts
to a Discord webhook whenever a player newly appears on the inactive list with
a total score of at least MIN_SCORE.

The first run quietly records everyone who is already inactive, so alerts start
with the inactives that appear after that. If IkaTracker can't be read for
WARN_AFTER_HOURS, a warning is posted in the channel (and an all-clear later).

    python nereus_inactive_alerts.py          keep running, check every POLL_MINUTES
    python nereus_inactive_alerts.py --once   one check, then exit (GitHub Actions / cron)
    python nereus_inactive_alerts.py --test   post a sample alert to check the webhook

Needs Python 3.8+ and nothing else.
"""
import argparse
import json
import os
import re
import sys
import time
from datetime import datetime, timezone
from html.parser import HTMLParser
from http.cookiejar import CookieJar
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode, urljoin
from urllib.request import HTTPCookieProcessor, Request, build_opener, urlopen

# ================================ SETTINGS ================================
# In Discord: Server Settings > Integrations > Webhooks > New Webhook > Copy Webhook URL
# On GitHub it comes from the NEREUS_WEBHOOK_URL secret, or DISCORD_WEBHOOK_URL if that's
# the only one you have.
WEBHOOK_URL = (os.environ.get("NEREUS_WEBHOOK_URL") or os.environ.get("DISCORD_WEBHOOK_URL")
               or "PASTE_YOUR_WEBHOOK_URL_HERE")

SERVER = "s70-en"      # IkaTracker server id (s70-en = Nereus, English)
MIN_SCORE = 100_000    # only alert on inactives with at least this total score
POLL_MINUTES = 15      # how often to check IkaTracker
MENTION = ""           # optional ping on each alert, e.g. "@here" or "<@&ROLE_ID>"
# ==========================================================================

BASE_URL = "https://ikatracker.com"
PER_PAGE = 100            # largest page size the site offers
MAX_PAGES = 30            # safety cap
FORGET_AFTER_HOURS = 72   # players gone from the list this long are forgotten,
                          # so they alert again if they go inactive again later
WARN_AFTER_HOURS = 6      # warn in Discord if IkaTracker has been unreadable this long
STATE_FILE = Path(__file__).resolve().with_name(f"inactive_state_{SERVER}.json")
USER_AGENT = "Mozilla/5.0 (compatible; IkaInactiveAlerts/1.0; Discord webhook notifier)"

_opener = build_opener(HTTPCookieProcessor(CookieJar()))


def log(msg):
    print(f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


# ------------------------------- page parsing -------------------------------

PLAYER_RE = re.compile(r"[?&]player_id=(\d+)")
PAGE_RE = re.compile(r"[?&]page=(\d+)")
_NUM = r"\d{1,3}(?:[,.'\u00a0\u202f ]\d{3})+|\d+"   # 528,924 / 528.924 / 528 924 / 714
NUMBER_RE = re.compile(_NUM)
NUMBER_IN_TEXT_RE = re.compile(rf"(?<!\w)(?:{_NUM})(?!\w)")
DAYS_RE = re.compile(r"^\d+\s*[^\W\d_]")             # "2 days"


def _to_int(text):
    return int(re.sub(r"\D", "", text))


class _TableParser(HTMLParser):
    """Collects table rows (cell text + links) and pagination page numbers."""

    SKIP = {"script", "style", "svg"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.header, self.rows, self.pages = [], [], set()
        self._row = self._cell = self._link = None
        self._skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in self.SKIP:
            self._skip += 1
        elif tag == "tr":
            self._close_row()
            self._row = []
        elif tag in ("td", "th"):
            self._close_cell()
            if self._row is not None:
                self._cell = {"th": tag == "th", "text": [], "links": []}
        elif tag == "a":
            href = dict(attrs).get("href") or ""
            m = PAGE_RE.search(href)
            if m and "recent_inactives" in href:
                self.pages.add(int(m.group(1)))
            if self._cell is not None:
                self._close_link()
                self._link = (href, [])
        elif tag == "br" and self._cell is not None:
            self._cell["text"].append(" ")

    def handle_endtag(self, tag):
        if tag in self.SKIP:
            self._skip = max(0, self._skip - 1)
        elif tag == "a":
            self._close_link()
        elif tag in ("td", "th"):
            self._close_cell()
        elif tag in ("tr", "thead", "tbody", "table"):
            self._close_row()

    def handle_data(self, data):
        if self._skip or self._cell is None:
            return
        self._cell["text"].append(data)
        if self._link is not None:
            self._link[1].append(data)

    def _close_link(self):
        if self._link is not None and self._cell is not None:
            href, parts = self._link
            self._cell["links"].append((href, " ".join("".join(parts).split())))
        self._link = None

    def _close_cell(self):
        self._close_link()
        if self._cell is not None and self._row is not None:
            self._cell["text"] = " ".join("".join(self._cell["text"]).split())
            self._row.append(self._cell)
        self._cell = None

    def _close_row(self):
        self._close_cell()
        row, self._row = self._row, None
        if not row:
            return
        if all(c["th"] for c in row):
            if not self.header and len(row) >= 3:
                self.header = [c["text"].lower() for c in row]
        else:
            self.rows.append(row)


def parse_page(html):
    """Return (players, last_page_number) for one page of the inactive list."""
    p = _TableParser()
    p.feed(html)
    p.close()
    p._close_row()

    def column(word):
        return next((i for i, h in enumerate(p.header) if word in h), None)

    score_col, days_col = column("score"), column("day")
    players = []
    for cells in p.rows:
        # The player cell is the one linking to a player page.
        pi = pid = name = None
        for i, cell in enumerate(cells):
            for href, text in cell["links"]:
                m = PLAYER_RE.search(href)
                if m:
                    pi, pid, name = i, m.group(1), text or cell["text"]
                    break
            if pid:
                break
        if pid is None:
            continue
        rest = cells[pi + 1:]
        by_header = cells[score_col]["text"] if score_col is not None and score_col < len(cells) else ""

        # Total score: the "score" column, else the first plain-number cell after the player.
        score = None
        if NUMBER_RE.fullmatch(by_header):
            score = _to_int(by_header)
        else:
            plain = next((c["text"] for c in rest if NUMBER_RE.fullmatch(c["text"])), None)
            if plain:
                score = _to_int(plain)
            else:
                m = NUMBER_IN_TEXT_RE.search(by_header)
                score = _to_int(m.group()) if m else None
        if score is None:
            continue

        world = alliance = alliance_url = None
        for cell in rest:
            for href, text in cell["links"]:
                if "type=alliance" in href:
                    alliance = text or cell["text"]
                    alliance_url = urljoin(BASE_URL + "/", href)
                elif world is None and "server=" in href and cell["text"]:
                    world = cell["text"]

        days = ""
        if days_col is not None and days_col < len(cells):
            days = cells[days_col]["text"]
        else:
            days = next((c["text"] for c in rest if DAYS_RE.match(c["text"])
                         and not any("type=alliance" in h for h, _ in c["links"])), "")

        players.append({
            "id": pid,
            "name": name or f"Player {pid}",
            "score": score,
            "alliance": alliance,
            "alliance_url": alliance_url,
            "world": world or SERVER,
            "days": days,
            "url": f"{BASE_URL}/atlas/search?player_id={pid}",
        })
    return players, max(p.pages, default=1)


# ------------------------------- IkaTracker -------------------------------

def http_get(url):
    req = Request(url, headers={
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "en-US,en;q=0.8",
    })
    for attempt in range(3):
        try:
            with _opener.open(req, timeout=30) as resp:
                return resp.read().decode(resp.headers.get_content_charset() or "utf-8", "replace")
        except HTTPError as e:
            if e.code == 403:
                raise RuntimeError("IkaTracker refused the request (HTTP 403); "
                                   "its Cloudflare protection may be blocking scripts") from None
            if (e.code < 500 and e.code != 429) or attempt == 2:
                raise RuntimeError(f"IkaTracker returned HTTP {e.code}") from None
        except (URLError, OSError) as e:
            if attempt == 2:
                raise RuntimeError(f"couldn't reach IkaTracker ({getattr(e, 'reason', e)})") from None
        time.sleep(10 * (attempt + 1))


def list_url(page):
    query = {"server": SERVER, "per_page": PER_PAGE, "dir": "asc"}
    if page > 1:
        query["page"] = page
    return f"{BASE_URL}/atlas/recent_inactives?{urlencode(query)}"


def fetch_inactives():
    """Read every page of the list. Returns (players, complete)."""
    players, ids = [], set()
    page = last = 1
    while page <= last:
        if page > MAX_PAGES:
            return players, False
        if page > 1:
            time.sleep(2)  # go easy on a free, volunteer-run site
        try:
            found, last_link = parse_page(http_get(list_url(page)))
        except Exception as e:
            if page == 1:
                raise
            log(f"Couldn't read page {page} ({e}); using the pages read so far.")
            return players, False
        fresh = [p for p in found if p["id"] not in ids]
        if not fresh:
            break
        players += fresh
        ids.update(p["id"] for p in fresh)
        last = max(last, last_link)
        page += 1
    if not players:
        raise RuntimeError("no players found on the page; IkaTracker may be down "
                           "or its layout may have changed")
    return players, True


# --------------------------------- Discord ---------------------------------

class WebhookError(RuntimeError):
    """The webhook URL is wrong or was deleted; retrying won't help."""


def _retry_after(err, body):
    try:
        return min(60.0, float(err.headers.get("Retry-After")) + 0.5)
    except (TypeError, ValueError):
        pass
    try:
        wait = float(json.loads(body).get("retry_after", 5))
        return min(60.0, (wait / 1000 if wait > 100 else wait) + 0.5)
    except Exception:
        return 5.0


def post_to_discord(payload):
    body = json.dumps(payload).encode("utf-8")
    for attempt in range(5):
        req = Request(WEBHOOK_URL, data=body, method="POST",
                      headers={"Content-Type": "application/json", "User-Agent": USER_AGENT})
        try:
            with urlopen(req, timeout=30):
                return
        except HTTPError as e:
            try:
                detail = e.read().decode("utf-8", "replace")[:300]
            except Exception:
                detail = ""
            if e.code == 429:
                wait = _retry_after(e, detail)
                log(f"Discord rate limit; waiting {wait:.1f}s")
                time.sleep(wait)
                continue
            if e.code in (401, 403, 404):
                raise WebhookError(f"Discord rejected the webhook (HTTP {e.code}); "
                                   "check the webhook URL") from None
            if e.code < 500:
                raise RuntimeError(f"Discord returned HTTP {e.code}: {detail}") from None
        except (URLError, OSError):
            pass
        time.sleep(5 * (attempt + 1))
    raise RuntimeError("couldn't post to Discord after several attempts")


def make_embed(p):
    tag, link = p.get("alliance"), p.get("alliance_url")
    if tag and link and not re.search(r"[\[\]()]", tag):
        alliance = f"[{tag}]({link.replace('(', '%28').replace(')', '%29').replace(' ', '%20')})"
    else:
        alliance = tag or "—"
    return {
        "title": f"💤 {p['name']}"[:256],
        "url": p["url"],
        "description": f"[Open inactive map]({BASE_URL}/map?server={SERVER}&state=inactive)",
        "color": 0xF1C40F if p["score"] >= 1_000_000 else 0xE67E22,
        "fields": [
            {"name": "Total score", "value": f"{p['score']:,}", "inline": True},
            {"name": "Alliance", "value": alliance[:1024], "inline": True},
            {"name": "Inactive for", "value": (p.get("days") or "—")[:1024], "inline": True},
        ],
        "footer": {"text": f"{p['world']} · IkaTracker"[:2048]},
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


def post_alerts(batch, total, first):
    payload = {
        "embeds": [make_embed(p) for p in batch],
        "allowed_mentions": {"parse": ["everyone", "roles", "users"] if MENTION else []},
    }
    if first:
        plural = "s" if total != 1 else ""
        payload["content"] = (f"{MENTION} **{total} new inactive player{plural}** with "
                              f"{MIN_SCORE:,}+ total score on {batch[0]['world']}").strip()
    post_to_discord(payload)


# ---------------------------------- state ----------------------------------

def load_state():
    if STATE_FILE.exists():
        try:
            state = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            if isinstance(state, dict) and isinstance(state.get("players"), dict):
                return state
        except (OSError, ValueError) as e:
            log(f"Couldn't read {STATE_FILE.name} ({e}); starting fresh.")
    return {"seeded": False, "players": {}}


def save_state(state):
    text = json.dumps(state, indent=1, ensure_ascii=False, sort_keys=True)
    try:
        if STATE_FILE.read_text(encoding="utf-8") == text:
            return  # unchanged: don't touch the file
    except OSError:
        pass
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, STATE_FILE)


def _record(p, now):
    return {"name": p["name"], "score": p["score"], "first_seen": now}


def note_failure(state, err):
    """Remember when problems started; warn in Discord once they've lasted a while."""
    now = int(time.time())
    hours = (now - state.setdefault("failing_since", now)) / 3600
    if hours >= WARN_AFTER_HOURS and not state.get("failure_warned"):
        try:
            post_to_discord({
                "content": (f"⚠️ Inactive alerts for **{SERVER}** have been failing for "
                            f"{hours:.0f} hours: {err}. Still retrying; I'll post here when "
                            "it's working again."),
                "allowed_mentions": {"parse": []},
            })
            state["failure_warned"] = True
        except Exception as e:
            log(f"Couldn't post the warning to Discord either: {e}")
    save_state(state)


def note_recovery(state):
    if state.pop("failing_since", None) is not None and state.pop("failure_warned", False):
        try:
            post_to_discord({"content": f"✅ Inactive alerts for **{SERVER}** are working again.",
                             "allowed_mentions": {"parse": []}})
        except Exception as e:
            log(f"Discord error: {e}")


# ---------------------------------- main ----------------------------------

def check(state):
    players, complete = fetch_inactives()
    note_recovery(state)
    now = int(time.time())
    known = state["players"]

    if not state.get("seeded"):
        if not complete:
            log("Couldn't read the whole list yet; will record existing inactives next check.")
            save_state(state)
            return
        for p in players:
            known[p["id"]] = _record(p, now)
        state["seeded"] = True
        save_state(state)
        log(f"First run: recorded {len(players)} players who are already inactive. "
            "Only new ones will be announced from now on.")
        try:
            post_to_discord({
                "content": (f"👀 Now watching **{players[0]['world']}** for new inactive players "
                            f"with **{MIN_SCORE:,}+** total score. The {len(players)} players "
                            "already inactive won't be announced."),
                "allowed_mentions": {"parse": []},
            })
        except WebhookError:
            raise
        except Exception as e:
            log(f"Discord error: {e}")
        return

    present = {p["id"] for p in players}
    for pid, rec in known.items():
        if pid in present:
            rec.pop("missing_since", None)
        elif complete:
            rec.setdefault("missing_since", now)
    new = [p for p in players if p["id"] not in known]
    quiet = [p for p in new if p["score"] < MIN_SCORE]
    alerts = sorted((p for p in new if p["score"] >= MIN_SCORE), key=lambda p: -p["score"])
    for p in quiet:
        known[p["id"]] = _record(p, now)

    sent = 0
    try:
        for i in range(0, len(alerts), 10):
            if i:
                time.sleep(2)
            batch = alerts[i:i + 10]
            post_alerts(batch, len(alerts), first=(i == 0))
            for p in batch:
                known[p["id"]] = _record(p, now)
                log(f"Alert sent: {p['name']} ({p['score']:,})")
            sent += len(batch)
    except WebhookError:
        raise
    except Exception as e:
        log(f"Discord error: {e}. Unsent alerts will be retried next check.")
    finally:
        if complete:
            cutoff = now - FORGET_AFTER_HOURS * 3600
            for pid in [k for k, v in known.items() if v.get("missing_since", now) < cutoff]:
                del known[pid]
        save_state(state)

    if new:
        log(f"{len(players)} inactive now: {sent} alert(s) sent, "
            f"{len(quiet)} new below {MIN_SCORE:,} ignored.")
    else:
        log(f"{len(players)} inactive now: nothing new.")


def send_test():
    found, _ = parse_page(http_get(list_url(1)))
    if not found:
        raise RuntimeError("no players found on the page")
    sample = next((p for p in found if p["score"] >= MIN_SCORE), found[0])
    log(f"Read {len(found)} players from IkaTracker; sending a sample alert for "
        f"{sample['name']} ({sample['score']:,}).")
    post_to_discord({
        "content": "🧪 **Test message**: new-inactive alerts will look like this.",
        "embeds": [make_embed(sample)],
        "allowed_mentions": {"parse": []},
    })
    log("Test alert sent. Check your Discord channel.")


def main():
    ap = argparse.ArgumentParser(description="Discord alerts for new inactive players on IkaTracker.")
    ap.add_argument("--once", action="store_true", help="run a single check and exit")
    ap.add_argument("--test", action="store_true", help="send a sample alert to Discord and exit")
    args = ap.parse_args()
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass

    if not WEBHOOK_URL.startswith("http"):
        sys.exit("Set WEBHOOK_URL at the top of this script (or the NEREUS_WEBHOOK_URL / "
                 "DISCORD_WEBHOOK_URL environment variable) to your Discord webhook URL.")
    try:
        if args.test:
            try:
                send_test()
            except Exception as e:
                log(f"Test failed: {e}")
                sys.exit(1)
            return

        state = load_state()
        log(f"Watching {SERVER} for new inactives with {MIN_SCORE:,}+ total score"
            + ("" if args.once else f", checking every {POLL_MINUTES} min (Ctrl+C to stop)"))
        while True:
            try:
                check(state)
            except WebhookError as e:
                log(f"Discord error: {e}")
                if args.once:
                    sys.exit(1)
            except Exception as e:
                log(f"Check failed: {e}")
                if os.environ.get("GITHUB_ACTIONS") == "true":
                    print(f"::warning::{e}", flush=True)
                note_failure(state, e)
            if args.once:
                return
            time.sleep(POLL_MINUTES * 60)
    except KeyboardInterrupt:
        log("Stopped.")


if __name__ == "__main__":
    main()
