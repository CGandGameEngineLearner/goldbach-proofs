import hashlib
import hmac
import ipaddress
import json
import gzip
import os
import re
import sqlite3
import ssl
import time
from contextlib import closing
from datetime import datetime
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from threading import BoundedSemaphore
from urllib.parse import parse_qs, urlsplit

from desk import Desk, QUEUE_BATCH
from landau import BASELINE, exponent_record
from presence import SitePresence
from zhihu_oauth import BASE as ZHIHU_PATH, ZhihuOAuth
import sponsors

SPONSOR_UPLOAD_SLOT = BoundedSemaphore(1)

ROOT = Path(__file__).resolve().parent
SITE_REVISION_FILE = ROOT / ".site-revision"
SITE_REVISION = SITE_REVISION_FILE.read_text(encoding="ascii").strip() if SITE_REVISION_FILE.is_file() else None
CREDS = Path(os.environ["CREDENTIALS_DIRECTORY"])
SECRET = (CREDS / "webhook").read_bytes().strip()
DB = Path(os.environ["STATE_DIRECTORY"]) / "verdicts.sqlite3"
oauth_credential = CREDS / "zhihu-oauth"
ZHIHU = ZhihuOAuth(DB.with_name("contributor-links.sqlite3"), json.loads(oauth_credential.read_bytes())
                   if oauth_credential.is_file() else None)
LIVE_RELEASE = Path("/opt/goldbach-catalogues/current")
CATALOGUE_ROOT = LIVE_RELEASE.resolve(strict=True) if LIVE_RELEASE.is_symlink() else ROOT
RELEASE_SHA = (CATALOGUE_ROOT / "revision").read_text() if CATALOGUE_ROOT != ROOT else None
GOLDBACH_CATALOGUE = json.loads((CATALOGUE_ROOT / "gaps.json").read_text(encoding="utf-8"))
GAPS = GOLDBACH_CATALOGUE["gaps"]
DESK = Desk(DB, GAPS, SECRET)
PROBLEM_FILE = CATALOGUE_ROOT / "problems.json"
PROBLEMS = json.loads(PROBLEM_FILE.read_text(encoding="utf-8")) if PROBLEM_FILE.exists() else {}
PUBLIC_SITE = "https://www.movan.tech/goldbach/"
problem_ids = set(gap["id"] for gap in GAPS)
for slug, problem in PROBLEMS.items():
    if slug in {"goldbach", DB.stem} or not re.fullmatch(r"[a-z]+(?:-[a-z]+)*", slug):
        raise ValueError(f"Invalid problem slug: {slug}")
    for gap in problem["gaps"]:
        if gap["id"] in problem_ids or not gap["id"].startswith(f"L-{slug}-"):
            raise ValueError(f"Invalid or duplicate task: {gap['id']}")
        problem_ids.add(gap["id"])
DESKS = {"goldbach": DESK, **{
    slug: Desk(DB.with_name(slug + ".sqlite3"), problem["gaps"], SECRET)
    for slug, problem in PROBLEMS.items()
}}
GAP_DESKS = {
    gap_id: slug for slug, desk in DESKS.items() for gap_id in desk.gaps
}
PRESENCE = SitePresence(DESKS.values())
PAGE_VIEWS_DB = DB.with_name("page-views.sqlite3")
IP_KEY_PATH = DB.with_name("ip-count.key")
if not IP_KEY_PATH.exists():
    with os.fdopen(os.open(IP_KEY_PATH, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), "wb") as key_file:
        key_file.write(os.urandom(32))
IP_KEY = IP_KEY_PATH.read_bytes()
if len(IP_KEY) != 32:
    raise ValueError("Invalid IP statistics key")
with closing(sqlite3.connect(PAGE_VIEWS_DB)) as conn, conn:
    conn.execute("CREATE TABLE IF NOT EXISTS visitor_ips (digest BLOB PRIMARY KEY) WITHOUT ROWID")
    conn.execute("CREATE TABLE IF NOT EXISTS page_views (source TEXT PRIMARY KEY, total INTEGER NOT NULL)")
    conn.execute("INSERT OR IGNORE INTO page_views VALUES ('live', 0)")

ASSETS = {
    "/core-team-signup.png": "image/png",
    sponsors.STYLE: "text/css",
    sponsors.SCRIPT: "text/javascript",
    "/wechat.svg": "image/svg+xml",
    "/discussion-qr.png": "image/png",
    "/discussion.js": "text/javascript",
    "/presence.js": "text/javascript",
    "/goldbach-icon.svg": "image/svg+xml",
    "/site.css": "text/css",
    "/site.js": "text/javascript",
    "/join.txt": "text/plain",
    "/join-zh.txt": "text/plain",
}

DISCUSSION_EXPIRES = datetime.fromisoformat("2026-12-02T00:00:00+08:00")


def discussion_widget(lang, prefix):
    if time.time() >= DISCUSSION_EXPIRES.timestamp():
        return ""
    zh = lang == "zh"
    label = "扫码进群 讨论进度" if zh else "Join WeChat group"
    name = "知乎 AI4S 讨论组（哥猜 3 群）" if zh else "Zhihu AI4S Goldbach discussion group 3"
    instructions = "微信扫码，讨论研究进度" if zh else "Scan in WeChat to discuss research progress"
    cutoff = DISCUSSION_EXPIRES.date()
    validity = f"{cutoff.month} 月 {cutoff.day} 日前有效" if zh else f"Valid before {cutoff:%Y-%m-%d} (UTC+8)"
    alt = "知乎 AI4S 讨论组（哥猜 3 群）微信群二维码" if zh else "WeChat QR code for the Zhihu AI4S Goldbach discussion group 3"
    return f"""<details class="discussion-widget" id="wechat-discussion" name="research-qr" aria-label="{name}"><summary><img class="wechat-mark" src="{prefix}wechat.svg" width="34" height="34" alt="">{label}<span aria-hidden="true"></span></summary>
<div class="discussion-body"><strong>{name}</strong><p>{instructions}</p>
<div class="discussion-code"><img src="{prefix}discussion-qr.png" alt="{alt}" width="360" height="566"></div>
<small>{validity}</small></div></details>"""


def core_team_signup(lang, prefix):
    if lang == "zh":
        title = "中心组报名"
        intro = "中心组由数学界专业人士和软件开发者组成。"
        research = "数学专业研究者负责制定研究路线、拆解子命题证明任务，并动态调整证明路线。"
        development = "软件开发者负责维护网站的基础设施。"
        caption = "扫码报名中心组"
    else:
        title = "Join the core team"
        intro = "The core team brings together professional mathematics researchers and software developers."
        research = "Mathematics researchers set the research direction, break it into proof tasks, and adjust the roadmap as results come in."
        development = "Software developers maintain the website infrastructure."
        caption = "Scan to apply"
    return f"""<details class="discussion-widget" id="core-team" name="research-qr">
<summary>{title}<span aria-hidden="true"></span></summary>
<div class="core-team-signup"><p>{intro}</p>
<p><strong>{research}</strong> {development}</p>
<figure><img src="{prefix}core-team-signup.png" width="176" height="176" alt="{caption}">
<figcaption>{caption}</figcaption></figure></div></details>"""


def site_dock(lang, prefix):
    zh = lang == "zh"
    visitors = "在线访客" if zh else "Visitors online"
    agents = "在研 Agent" if zh else "Working agents"
    views = "累计浏览量" if zh else "Total page views"
    ips = "累计独立 IP" if zh else "Unique IP addresses"
    detail = ("累计浏览量统计首页、问题目录和研究页的成功访问，刷新也计一次。近 90 秒内浏览可见页面的浏览器，同一域名多标签合计一次。"
              "累计独立 IP 包含历史日志中可确认的页面访问，两个域名下同一来源 IP 合计一次。"
              "在研 Agent 按尚未提交且有效的任务租约计，每份一席。每 30 秒刷新。" if zh else
              "Page views count successful loads of the home, directory and research pages, including reloads. "
              "Online visitors have a visible page in the last 90 seconds. Tabs on the same domain count once. "
              "Unique IPs include historical page visits matched to access logs. Each source IP counts once across both domains. "
              "Each active, unsubmitted research lease counts as one agent seat. Updates every 30 seconds.")
    return f"""<aside class="discussion-dock" aria-label="{'研究台动态' if zh else 'Research desk activity'}">
<details class="presence-widget" data-endpoint="{prefix}api/presence" hidden>
<summary><span><i aria-hidden="true"></i>{visitors} <b data-count="visitors">—</b></span>
<span>{agents} <b data-count="agents">—</b></span>
<span class="total-views">{views} <b data-count="page_views">—</b></span>
<span class="total-views">{ips} <b data-count="unique_ips">—</b></span></summary>
<p>{detail}</p></details>
{discussion_widget(lang, prefix)}{core_team_signup(lang, prefix)}</aside>
<script src="{prefix}discussion.js" defer></script><script src="{prefix}presence.js" defer></script>"""


def research_status(desk=DESK):
    db = desk.db_path
    results = []
    latest = {}
    attempts = 0
    extra = {}
    if db.exists():
        with closing(sqlite3.connect(db.as_uri() + "?mode=ro", uri=True)) as conn:
            conn.execute("BEGIN")
            if desk is DESKS.get("quadratic-primes"):
                extra["lpf_record"] = exponent_record(desk, conn)
            if conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='verdicts'").fetchone():
                results = [json.loads(body) for (body,) in conn.execute(
                    "SELECT body FROM verdicts ORDER BY run_id DESC, attempt DESC LIMIT 12"
                )]
                rows = conn.execute("""
                    WITH runs AS (
                        SELECT body, run_id, attempt,
                               json_extract(CAST(body AS TEXT), '$.lemma_id') AS lemma,
                               json_extract(CAST(body AS TEXT), '$.verdict') AS verdict
                        FROM verdicts
                    ), ranked AS (
                        SELECT body, lemma,
                               ROW_NUMBER() OVER (
                                   PARTITION BY lemma ORDER BY run_id DESC, attempt DESC
                               ) AS position,
                               MAX(verdict = 'ACCEPTED') OVER (PARTITION BY lemma) AS proved,
                               COUNT(*) OVER (PARTITION BY lemma) AS attempts
                        FROM runs
                    )
                    SELECT lemma, body, proved, attempts FROM ranked WHERE position = 1
                """)
                for lemma, body, proved, count in rows:
                    latest[lemma] = (json.loads(body), bool(proved))
                    attempts += count

    gaps = []
    for gap in desk.gaps.values():
        result, proved = latest.get(gap["id"], (None, False))
        gaps.append({**gap, "latest": result, "proved": proved})
    accepted = sum(gap["proved"] for gap in gaps)
    desk_status = desk.public_status()
    rankings = desk_status["rankings"]
    rows = rankings["all_time"] + rankings["hour"]
    profiles = ZHIHU.public_profiles(sorted({row["handle"].lower() for row in rows}))
    for row in rows:
        profile = profiles.get(row["handle"].lower())
        if profile:
            row["zhihu"] = profile
    return {
        **extra,
        "catalogue_revision": RELEASE_SHA,
        "gaps": gaps,
        "results": results,
        "desk": desk_status,
        "counts": {
            "published": len(gaps),
            "accepted": accepted,
            "open": len(gaps) - accepted,
            "attempts": attempts,
        },
    }

def goldbach_task_routes(lang):
    zh = lang == "zh"
    heading = "按子命题领取" if zh else "Choose a proof task"
    note = ("展开路线，查看每个子命题的声明和领取入口。" if zh else
            "Expand a track to inspect its statements and choose a task.")
    tracks = GOLDBACH_CATALOGUE.get("tracks", [])
    names = {track["id"]: track["title"][lang] for track in tracks}
    sections = []
    for track in tracks:
        links = []
        for gap in GAPS:
            if gap.get("track") != track["id"]:
                continue
            key = escape(gap["id"])
            prefix = {"target": "待突破 · " if zh else "Research target · ",
                      "conditional": "条件归约 · " if zh else "Conditional · "}.get(gap.get("role"), "")
            links.append(f'<a href="?lang={lang}&amp;lemma={key}#roadmap" data-roadmap-task="{key}">'
                         f'{prefix}{escape(gap["plain_statement"][lang])}</a>')
        uses = " · ".join(f'<a href="#track-{key}">{escape(names[key])}</a>' for key in track["feeds"])
        next_steps = f'<p>{"用于" if zh else "Feeds into"}　{uses}</p>' if uses else ""
        sections.append(f'<details id="track-{track["id"]}"><summary>{escape(names[track["id"]])} ({len(links)})</summary>'
                        f'<p>{escape(track["description"][lang])}</p>{next_steps}<div class="roadmap-tasks">'
                        f'{"".join(links)}</div></details>')
    return f'<div class="goldbach-tracks"><h3>{heading}</h3><p>{note}</p>{"".join(sections)}</div>'


def goldbach_roadmap_page(page, lang):
    # Catalogue order sets the two featured tracks; all tracks remain in the task list.
    if RELEASE_SHA:
        page = page.replace("</head>", f'<meta name="catalogue-revision" content="{escape(RELEASE_SHA)}"></head>', 1)
    featured = GOLDBACH_CATALOGUE.get("tracks", [])[:2]
    cards, stages = [], []
    for track in featured:
        key = escape(track["id"])
        title = escape(track["title"][lang])
        summary = escape(track["description"][lang])
        count = sum(g.get("track") == track["id"] for g in GAPS)
        tasks = f"{count} 个子命题" if lang == "zh" else f"{count} proof tasks"
        cards.append(f'<button type="button" class="map-program-button" data-program="{key}" aria-pressed="false">'
                     f'<strong class="program-name">{title}</strong><span class="program-count">{tasks}</span></button>')
        stages.append(f'<li><h3>{title}</h3><p>{summary}</p><a href="#track-{key}">{tasks}</a></li>')
    overview = '<ul class="roadmap topic-roadmap">' + "".join(stages) + '</ul>'
    return page.replace("<!-- catalogue filters -->", "".join(cards)).replace(
        "<!-- catalogue roadmap -->", overview + goldbach_task_routes(lang))


def problem_page(page, slug, lang):
    data = PROBLEMS[slug]
    title, question, description = (escape(data[key][lang]) for key in ("title", "question", "summary"))
    zh = lang == "zh"
    translations = {
        "map": "研究地图" if zh else "Research map",
        "target": "研究起点" if zh else "Starting point",
        "road": "研究路线" if zh else "Research roadmap",
        "foundation": "基础引理" if zh else "Foundations",
        "correlation": "证明工具" if zh else "Proof techniques",
    }
    if slug == "quadratic-primes":
        translations["target"] = "大素因子指数" if zh else "Large prime factor exponent"
    page = page.replace('<body id="top">', f'<body id="top" data-problem="{slug}">')
    page = re.sub(r'<title>[^<]*</title>', f'<title>{title}</title>', page, count=1)
    page = re.sub(r'<meta (?:name|property)="(?:description|og:[^"]+|twitter:[^"]+)"[^>]*>\n?', '', page)
    page = re.sub(r'(<a href="#top" class="brand">.*?</span>)[^<]+', lambda m: m[1] + title, page, count=1)
    page = page.replace('aria-hidden="true">p + q ?</span>', f'aria-hidden="true">{escape(data["formula"])}</span>', 1)
    page = page.replace('href="problems/?', 'href="../?').replace('href="site.css"', 'href="../../site.css"').replace(
        'src="site.js"', 'src="../../site.js"')
    page = page.replace('href="goldbach-icon.svg"', 'href="../../goldbach-icon.svg"')
    page = page.replace('src="goldbach-icon.svg"', 'src="../../goldbach-icon.svg"')
    page = page.replace('href="auth/zhihu?', 'href="../../auth/zhihu?')
    page = re.sub(r'(<h1 id="page-title">).*?(</h1>)', lambda m: m[1] + title + m[2], page)
    page = re.sub(r'(<p class="hero-question">).*?(</p>)', lambda m: m[1] + question + m[2], page)
    page = re.sub(r'(<p class="hero-description">).*?(</p>)', lambda m: m[1] + description + m[2], page)
    page = page.replace("强猜想 · 尚未解决", "开放研究问题").replace("Strong conjecture · Open", "Open research problem")
    page = re.sub(r'(<h2 id="target-title">).*?(</h2>)',
                  lambda m: m[1] + translations["target"] + m[2], page)
    formula = escape(data["formula"])
    figure = f'<div class="target-figure topic-formula">{formula}</div>'
    if slug == "quadratic-primes":
        current = "当前研究指数" if zh else "Current research exponent"
        target = "目标指数" if zh else "Target exponent"
        condition = ("对无穷多个 n，存在整除 n² + 1 的素数 p，且 p > nᵅ。若能证明 α = 2，则 p 只能等于 n² + 1。" if zh else
                     "For infinitely many n, a prime p divides n² + 1 with p > nᵅ. At α = 2 this forces p = n² + 1.")
        source = ("外部基线证书" if zh else "External baseline certificate") + f' · {BASELINE["exponent"]}'
        status_link = "查看实时数据" if zh else "View live data"
        article = "https://www.cambridge.org/engage/coe/article-details/6aa045a1810b9dcc82ba1e4b"
        news = "最新成果" if zh else "Research news"
        headline = "n² + 1 的大素因子：指数达到 1.323" if zh else "Large prime factors of n² + 1 reach exponent 1.323"
        summary = ("这篇预印本报告，通过在 Harman 筛中递归使用 Buchstab 恒等式，可证明对无穷多个正整数 n，"
                   "存在素数 p 整除 n² + 1，且 p > n¹·³²³。这个界允许 n² + 1 还有其他因子。"
                   "本站以 1.323 为外部基线，下一步是提高这个指数。" if zh else
                   "The preprint reports that recursive Buchstab switching in a Harman sieve gives infinitely many "
                   "positive integers n for which a prime divisor p of n² + 1 exceeds n¹·³²³. Other factors may remain. "
                   "The project takes 1.323 as its external baseline and aims to raise the exponent.")
        read = "阅读预印本" if zh else "Read the preprint"
        close = "关闭" if zh else "Close"
        figure = (
            '<div class="lpf-record" id="lpf-record">'
            f'<dl class="lpf-values"><div><dt>{current} α</dt><dd id="lpf-current">—</dd></div>'
            f'<div><dt>{target}</dt><dd id="lpf-target">2</dd></div></dl>'
            '<p class="lpf-evidence" id="lpf-kind"></p><p id="lpf-verified"></p>'
            f'<p class="lpf-condition">{condition}</p>'
            f'<a href="{escape(BASELINE["source_url"])}">{source}</a>'
            f'<noscript> · <a href="api/status">{status_link}</a></noscript>'
            '<p id="lpf-notice" role="status"></p></div>'
            f'<a id="lpf-news-open" href="{article}">{news} · 1.323</a>'
            '<dialog class="rankings-dialog lpf-news" id="lpf-news" aria-labelledby="lpf-news-title">'
            f'<div class="rankings-dialog-heading"><span>{news}</span><form method="dialog"><button>{close}</button></form></div>'
            f'<h2 id="lpf-news-title">{headline}</h2><p><time datetime="2026-09-13">2026-09-13</time> · Cambridge Open Engage</p>'
            f'<p>{summary}</p><a href="{article}">{read} ↗</a></dialog>'
        )
    page = re.sub(r'<div class="target-figure".*?<div class="target-progress">',
                  lambda _: figure + '<div class="target-progress">', page, count=1, flags=re.S)
    page = re.sub(r'(<h2 id="lemma-title">).*?(</h2>)', lambda m: m[1] + title + ' · ' + translations["map"] + m[2], page)
    materials = data.get("materials", [])
    note_title = ("前期研究" if zh else "Prior research") if materials else translations["road"]
    note_body = escape(data["background"][lang]) if materials else description
    references = " · ".join(f'<a href="{escape(item["url"])}">{escape(item[lang])}</a>' for item in materials)
    page = re.sub(r'<aside class="method-note">.*?</aside>',
                  lambda _: f'<aside class="method-note"><h2>{note_title}</h2><p>{note_body}</p>{references}</aside>',
                  page, count=1, flags=re.S)
    def program_card(match):
        key = match[2]
        if key not in translations:
            return ""
        text = re.sub(r'(<strong class="program-name">).*?(</strong>)',
                      lambda m: m[1] + translations[key] + m[2], match[0])
        return re.sub(r'<span class="program-description">.*?</span>', '', text)
    page = re.sub(r'<button type="button" class="map-program-button" (data-program="([^"]+)").*?</button>',
                  program_card, page, flags=re.S)
    def roadmap_stage(step):
        heading, body = step[lang]
        links = "".join(
            f'<a href="?lang={lang}&amp;lemma={escape(task["id"])}#roadmap" '
            f'data-roadmap-task="{escape(task["id"])}">{escape(task[lang])}</a>'
            for task in step.get("tasks", [])
        )
        return (f'<li><h3>{escape(heading)}</h3><p>{escape(body)}</p>'
                f'<div class="roadmap-tasks">{links}</div></li>')

    stages = "".join(roadmap_stage(step) for step in data.get("roadmap", []))
    page = re.sub(r'<section class="section road-section" id="roadmap".*?</section>',
                  lambda _: f'<section class="section road-section" id="roadmap"><div class="section-heading"><div>'
                  f'<h2>{translations["road"]}</h2></div></div><ol class="roadmap topic-roadmap">{stages}</ol></section>',
                  page, count=1, flags=re.S)
    url = PUBLIC_SITE + "problems/" + slug + "/join" + ("-zh" if zh else "") + ".txt"
    prompt = (f"阅读 {url}，按说明领取一条任务，提交 Lean 证明并跟踪核验。" if zh else
              f"Read {url}, claim one task, and submit a Lean proof for verification.")
    page = re.sub(r'(<p id="agent-prompt"[^>]*>).*?(</p>)', lambda m: m[1] + escape(prompt) + m[2], page)
    return page


def problem_card(slug, data, lang):
    zh = lang == "zh"
    try:
        verified, published, available = DESKS[slug].progress()
    except sqlite3.Error:
        progress = "暂时无法读取进度" if zh else "Progress temporarily unavailable"
    else:
        progress = (f"Lean 已核验 {verified}/{published} · {available} 条可领取" if zh else
                    f"Lean verified {verified}/{published} · {available} available")
    return (f'<a class="problem-card" href="{slug}/?lang={lang}"><span class="problem-formula">{escape(data["formula"])}</span>'
            f'<h2>{escape(data["title"][lang])}</h2><p>{escape(data["question"][lang])}</p>'
            f'<p class="problem-progress">{progress}</p></a>')


def directory_page(lang):
    zh = lang == "zh"
    heading = "更多猜想" if zh else "Research problems"
    back = "返回强哥德巴赫猜想" if zh else "Back to Strong Goldbach"
    platform = "数学猜想协作平台" if zh else "Open Conjecture Platform"
    intro = ("数学家可以担任研究管理员，制定路线、拆分引理和审阅命题。选一道感兴趣的猜想，把参与提示词交给自己的 Agent，就可以从一条引理开始。" if zh else
             "Mathematicians can lead a research desk, plan its roadmap and review statements. Choose a problem and give its joining prompt to your agent to start with one lemma.")
    cards = "\n".join(problem_card(slug, data, lang) for slug, data in PROBLEMS.items())
    return f"""<!doctype html>
<html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{heading} · {platform}</title><link rel="icon" type="image/svg+xml" sizes="any" href="../goldbach-icon.svg"><link rel="stylesheet" href="../site.css"></head>
<body><header class="masthead"><div class="shell masthead-inner"><a class="brand" href="../?lang={lang}">{back}</a>
<a class="locale" href="?lang={'en' if zh else 'zh'}">{'English' if zh else '简体中文'}</a></div></header>
<main class="shell problem-directory"><div class="platform-credit"><img src="../goldbach-icon.svg" width="38" height="38" alt=""><strong>{platform}</strong></div><h1>{heading}</h1><p>{intro}</p><a href="https://github.com/CGandGameEngineLearner/goldbach-proofs">GitHub ↗</a><div class="problem-list">{cards}</div></main>{site_dock(lang, "../")}</body></html>"""


def queue_pending(raw_body, headers):
    if not DESK.signed(headers.get("X-Goldbach-Signature", ""), raw_body):
        return 401, {"error": "invalid_signature"}
    now = int(time.time())
    desks = tuple(DESKS.values())
    quota = max(1, QUEUE_BATCH // len(desks))
    rows = []
    for desk in desks:
        if len(rows) >= QUEUE_BATCH:
            break
        rows.extend(desk.pending(now, min(quota, QUEUE_BATCH - len(rows)))[1]["pending"])
    for desk in desks:
        if len(rows) >= QUEUE_BATCH:
            break
        rows.extend(desk.pending(now, QUEUE_BATCH - len(rows))[1]["pending"])
    return 200, {"pending": rows}


def china_networks():
    for line in (ROOT / "china-apnic.txt").read_text(encoding="utf-8").splitlines():
        fields = line.split("|")
        if len(fields) < 7 or fields[1] != "CN" or fields[6] not in {"allocated", "assigned"}:
            continue
        _, _, kind, start, size, *_ = fields
        if kind == "ipv4":
            first = ipaddress.IPv4Address(start)
            yield from ipaddress.summarize_address_range(first, first + int(size) - 1)
        if kind == "ipv6":
            yield ipaddress.IPv6Network(f"{start}/{size}")

NETWORKS = tuple(china_networks())

class Handler(BaseHTTPRequestHandler):
    def log_request(self, code="-", size="-"):
        if getattr(self, "path", "").partition("?")[0].startswith(ZHIHU_PATH):
            self.log_message("Zhihu authorization request %s", code)
        else:
            super().log_request(code, size)

    def zhihu_request(self, path, query=""):
        if self.command == "HEAD":
            return self.reply(405, b'{}')
        if self.command == "GET" and path == sponsors.DESK + "/upload-limit":
            return self.oauth_response(path, sponsors.upload_error(self.language(urlsplit(self.path))))
        if self.command == "POST" and path == sponsors.DESK + "/upload":
            return self.sponsor_upload(path)
        try:
            if self.command == "POST":
                size = int(self.headers.get("Content-Length", "0"))
                if not 0 < size <= 8192 or self.headers.get_content_type() != "application/x-www-form-urlencoded":
                    return self.reply(400, b'{}')
                self.connection.settimeout(8)
                query = self.rfile.read(size).decode("utf-8")
            if len(query) > 12000:
                return self.reply(400, b'{}')
            fields = parse_qs(query, keep_blank_values=True, max_num_fields=12)
            if any(len(vals) != 1 for vals in fields.values()):
                return self.reply(400, b'{}')
            status, headers, body = ZHIHU.handle(self.command, path, {k: v[0] for k, v in fields.items()}, self.headers)
        except (ValueError, OSError, sqlite3.Error):
            return self.reply(400, b'{}')
        return self.oauth_response(path, (status, headers, body))

    def sponsor_upload(self, path):
        lang = self.language(urlsplit(self.path))
        def notice(status, zh, en):
            return self.oauth_response(path, sponsors.upload_notice(status, lang, zh if lang == "zh" else en))

        self.connection.settimeout(8)
        try:
            size = int(self.headers.get("Content-Length", "0"))
            if size > sponsors.LIMIT:
                self.discard_upload(size)
                return self.oauth_response(path, sponsors.upload_error(lang))
            if self.headers.get("Origin") != sponsors.ORIGIN:
                self.discard_upload(size)
                return notice(403, "请从本站设置页重新提交。", "Resubmit from the site settings page.")
            if not ZHIHU.can_upload_sponsor(self.headers):
                self.discard_upload(size)
                return notice(403, "登录已过期，请重新登录知乎后提交。", "Your session expired. Sign in with Zhihu and retry.")
            if not SPONSOR_UPLOAD_SLOT.acquire(blocking=False):
                self.discard_upload(size)
                return self.oauth_response(path, sponsors.upload_error(lang, busy=True))
            try:
                raw = self.rfile.read(size) if size > 0 else b""
                if len(raw) != size or self.headers.get_content_type() != "multipart/form-data":
                    raise ValueError("incomplete upload")
                fields = sponsors.upload_fields(self.headers["Content-Type"], raw)
                fields["lang"] = lang
                result = ZHIHU.handle("POST", path, fields, self.headers)
            finally:
                SPONSOR_UPLOAD_SLOT.release()
        except (ValueError, RecursionError):
            return notice(400, "上传表单不完整，请重新选择图片后再试。", "The upload was incomplete. Select the image again and retry.")
        except TimeoutError:
            return notice(408, "上传超时，请重新提交。", "The upload timed out. Try again.")
        except sqlite3.Error:
            self.log_error("Sponsor submission database unavailable")
            return notice(503, "暂时无法保存投稿，请稍后重试。", "Submission could not be saved. Try again shortly.")
        return self.oauth_response(path, result)

    def discard_upload(self, size):
        # Drain a buffered proxy request so closing the TLS connection keeps the error response.
        remaining = min(size, 5 * 1024 * 1024)
        while remaining > 0:
            chunk = self.rfile.read(min(remaining, 64 * 1024))
            if not chunk:
                break
            remaining -= len(chunk)

    def oauth_response(self, path, result):
        status, headers, body = result
        self.send_response(status)
        for name, value in headers.items():
            self.send_header(name, value)
        self.send_header("Cache-Control", "no-store")
        # Form pages must preserve Origin on same-site POSTs for CSRF validation.
        policy = "same-origin" if path != ZHIHU_PATH + "/callback" else "no-referrer"
        self.send_header("Referrer-Policy", policy)
        self.send_header("Content-Security-Policy", "default-src 'none'; img-src 'self'; style-src 'self' 'unsafe-inline'; script-src 'self'; connect-src 'self'; form-action 'self' https://openapi.zhihu.com https://www.zhihu.com; frame-ancestors 'none'; base-uri 'none'")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def reply(self, status, body, content_type="application/json", language=None, encoding=None):
        if status == 200 and self.command == "GET" and content_type == "text/html":
            try:
                with closing(sqlite3.connect(PAGE_VIEWS_DB)) as conn, conn:
                    conn.execute("UPDATE page_views SET total = total + 1 WHERE source = 'live'")
                    ip = self.client_ip()
                    ip = getattr(ip, "ipv4_mapped", None) or ip
                    if not ip.is_loopback:
                        digest = hmac.digest(IP_KEY, ip.packed, "sha256")
                        conn.execute("INSERT OR IGNORE INTO visitor_ips VALUES (?)", (digest,))
            except sqlite3.Error:
                self.log_error("Page view counter unavailable")
        self.send_response(status)
        if content_type == "application/json" or content_type.startswith("text/"):
            content_type += "; charset=utf-8"
        self.send_header("Content-Type", content_type)
        if encoding:
            self.send_header("Content-Encoding", encoding)
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Length", str(len(body)))
        if language:
            self.send_header("Content-Language", language)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def client_ip(self):
        peer = ipaddress.ip_address(self.client_address[0])
        peer = getattr(peer, "ipv4_mapped", None) or peer
        if peer.is_loopback:
            forwarded = self.headers.get("X-Goldbach-Client-IP")
            if forwarded:
                try:
                    return ipaddress.ip_address(forwarded)
                except ValueError:
                    pass
        return peer

    def language(self, url):
        lang = parse_qs(url.query).get("lang", [""])[0]
        if lang in {"zh", "en"}:
            return lang
        return "zh" if any(self.client_ip() in net for net in NETWORKS) else "en"

    @staticmethod
    def scope(path):
        match = re.fullmatch(r"/problems/([a-z-]+)(/.*)", path)
        if match:
            return DESKS.get(match[1]) if match[1] in PROBLEMS else None, match[2], match[1]
        return DESK, path, "goldbach"

    def reply_presence(self, visitor=None):
        counts = PRESENCE.snapshot(visitor)
        try:
            with closing(sqlite3.connect(PAGE_VIEWS_DB)) as conn:
                counts["page_views"] = conn.execute("SELECT sum(total) FROM page_views").fetchone()[0]
                counts["unique_ips"] = conn.execute("SELECT count(*) FROM visitor_ips").fetchone()[0]
        except sqlite3.Error:
            counts["page_views"] = counts["unique_ips"] = None
        return self.reply(200, json.dumps(counts).encode())

    def do_GET(self):
        url = urlsplit(self.path)
        if url.path == "/api/presence":
            return self.reply_presence()
        logo = re.fullmatch(r"/sponsors/logo/([1-9][0-9]{0,15})\.png", url.path)
        if logo:
            image = sponsors.public_logo(ZHIHU.db, logo[1])
            return self.reply(200, image, "image/png") if image else self.reply(404, b'{}')
        if url.path == ZHIHU_PATH or url.path.startswith(ZHIHU_PATH + "/"):
            return self.zhihu_request(url.path, url.query)
        if url.path == "/problems" or url.path.removeprefix("/problems/") in PROBLEMS:
            self.send_response(308)
            suffix = "?" + url.query if url.query else ""
            self.send_header("Location", url.path.rsplit("/", 1)[-1] + "/" + suffix)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        if url.path == "/problems/":
            lang = self.language(url)
            directory = directory_page(lang).replace("</main>", "</main>" + sponsors.wall(ZHIHU.db,lang,"../"), 1)
            directory = directory.replace('</a></div></header>', '</a>'+ZHIHU.account_link(self.headers,lang)+'</div></header>',1)
            return self.reply(200, directory.encode(), "text/html", lang)
        desk, path, slug = self.scope(url.path)
        if desk is None:
            return self.reply(404, b'{}')
        if path == "/health":
            return self.reply(200, json.dumps({
                "status": "ok", "catalogue_revision": RELEASE_SHA,
                "site_revision": SITE_REVISION,
            }).encode())
        if path == "/research-changes":
            zh = self.language(url) == "zh"
            title = "研究路线变更记录" if zh else "Research change history"
            entries = json.loads((CATALOGUE_ROOT / "history.json").read_bytes()) if RELEASE_SHA else []
            repo = "https://github.com/CGandGameEngineLearner/goldbach-proofs"
            rows = "".join(
                f'<li><time>{escape(row["at"])}</time> · <a href="{repo}/pull/{int(row["pr"])}">'
                f'{escape(row["title"])}</a> · {escape(row["actor"])} · '
                f'<a href="{repo}/actions/runs/{int(row["run"])}">CI</a></li>'
                for row in reversed(entries))
            empty = "尚无自动发布记录。" if zh else "No automated releases yet."
            page = (f'<!doctype html><html lang="{"zh" if zh else "en"}"><meta charset="utf-8">'
                    f'<meta name="viewport" content="width=device-width,initial-scale=1"><title>{title}</title>'
                    f'<link rel="stylesheet" href="site.css"><main class="shell"><h1>{title}</h1>'
                    f'{("<ol>"+rows+"</ol>") if rows else empty}</main></html>')
            return self.reply(200, page.encode(), "text/html")
        if path == "/api/status":
            try:
                status = research_status(desk)
                web_view = parse_qs(url.query).get("view") == ["web-gzip"]
                if web_view:
                    for gap in status["gaps"]:
                        if gap["latest"]:
                            gap["latest"] = {k: v for k, v in gap["latest"].items() if k != "manifest"}
                body = json.dumps(status, ensure_ascii=False, separators=(",", ":")).encode()
            except sqlite3.Error as error:
                self.log_error("Unable to read verdicts: %s", error)
                return self.reply(503, b'{"error":"verdicts unavailable"}')
            if web_view:
                return self.reply(200, gzip.compress(body, compresslevel=3), encoding="gzip")
            return self.reply(200, body)
        if path == "/platform-logo.svg":
            path = "/goldbach-icon.svg"
        if path in ASSETS:
            asset = ROOT / path[1:]
            if not asset.is_file():
                return self.reply(404, b'{}')
            content = asset.read_bytes()
            if slug != "goldbach" and path in {"/join.txt", "/join-zh.txt"}:
                lang = "zh" if path.endswith("-zh.txt") else "en"
                title = PROBLEMS[slug]["title"][lang]
                introduction = (f"请使用自己的 GitHub 账号，领取并提交一条「{title}」的 Lean 4 引理。"
                                "只有通过权威 Lean 核验的引理才会记入研究台。" if lang == "zh" else
                                f"Use your GitHub account to claim and submit one Lean 4 lemma for {title}. "
                                "The desk credits lemmas that pass authoritative Lean verification.")
                if materials := PROBLEMS[slug].get("materials"):
                    introduction += "\n" + PROBLEMS[slug]["background"][lang] + "\n" + "\n".join(
                        f'{item[lang]}  {item["url"]}' for item in materials
                    )
                if slug == "quadratic-primes":
                    introduction += (
                        "\n研究目标是尽可能提高指数 α。先查看问题页的当前纪录，再领取解析转移、筛法估计或指数挑战。"
                        "1.32301 与 1.324 可并行尝试；其他改进值可在 research/problems.json 提交新任务 PR。"
                        "纪录要求对无穷多个 n 证明存在素因子 p ∣ n²+1 且 p > nᵅ。" if lang == "zh" else
                        "\nAim for the largest provable exponent. Check the current record, then claim an analytic transfer, "
                        "sieve estimate or exponent challenge. Try 1.32301 or 1.324 in parallel, or propose another threshold "
                        "by PR to research/problems.json. A record requires a prime divisor p of n²+1 exceeding nᵅ for infinitely many n."
                    )
                _, _, instructions = asset.read_text(encoding="utf-8").split("\n\n", 2)
                if materials:
                    instructions = instructions.replace("不要提交固定偶数或有限闭区间的枚举结果。", "证明须覆盖所领取命题中的全部输入。").replace(
                        "Fixed-input and finite-range enumeration are outside this research program.",
                        "Cover the full range of inputs in the claimed proposition."
                    )
                instructions = instructions.replace(
                    "\npython tools/goldbach.py claim\n", f"\npython tools/goldbach.py claim --problem {slug}\n"
                )
                instructions = instructions.replace("https://www.goldbach.tech/#records\n", "").replace(
                    PUBLIC_SITE + "#records", f"{PUBLIC_SITE}problems/{slug}/?lang={lang}#records"
                )
                content = f"{title}\n\n{introduction}\n\n{instructions}".encode()
            return self.reply(200, content, ASSETS[path])
        if path != "/":
            return self.reply(404, b'{}')
        lang = self.language(url)
        page = (ROOT / f"{lang}.html").read_text(encoding="utf-8")
        if slug != "goldbach":
            page = problem_page(page, slug, lang)
        else:
            page = goldbach_roadmap_page(page, lang)
        prefix = "" if slug == "goldbach" else "../../"
        page = page.replace("<!-- account -->", ZHIHU.account_link(self.headers, lang), 1)
        hero = '<section class="hero" aria-labelledby="page-title">'
        page = page.replace(hero, sponsors.wall(ZHIHU.db, lang, prefix) + hero, 1)
        page = page.replace("</body>", site_dock(lang, prefix) + "</body>", 1)
        self.reply(200, page.encode(), "text/html", lang)

    do_HEAD = do_GET

    def desk_post(self, desk, path, slug):
        try:
            size = int(self.headers.get("Content-Length", "0"))
            if not 1 <= size <= 8192:
                return self.reply(413, b'{"error":"request body must be between 1 and 8192 bytes"}')
            self.connection.settimeout(10)
            raw = self.rfile.read(size)
            body = json.loads(raw)
            if not isinstance(body, dict):
                raise ValueError()
            if path == "/api/desk/pending" and slug == "goldbach":
                status, result = queue_pending(raw, self.headers)
            else:
                if path == "/api/desk/authorize" and slug == "goldbach":
                    gap = body.get("gap")
                    if isinstance(gap, str):
                        desk = DESKS[GAP_DESKS.get(gap, "goldbach")]
                status, result = desk.dispatch(path, body, self.headers, str(self.client_ip()), raw)
        except (ValueError, OSError):
            return self.reply(400, b'{"error":"invalid request body"}')
        except sqlite3.Error as error:
            self.log_error("Desk unavailable: %s", error)
            return self.reply(503, b'{"error":"task desk temporarily unavailable"}')
        return self.reply(status, json.dumps(result, ensure_ascii=False).encode())

    def do_POST(self):
        if self.path == "/api/presence":
            visitor = self.headers.get("X-Goldbach-Visit", "")
            if not re.fullmatch(r"[0-9a-f]{32}", visitor):
                return self.reply(400, b'{"error":"invalid presence identifier"}')
            return self.reply_presence(visitor)
        if self.path.startswith(ZHIHU_PATH + "/"):
            return self.zhihu_request(urlsplit(self.path).path)
        desk, path, slug = self.scope(self.path)
        if desk is not None and path.startswith("/api/desk/"):
            return self.desk_post(desk, path, slug)
        if slug != "goldbach" or path != "/api/verdict":
            return self.reply(404, b'{}')
        try:
            self.connection.settimeout(10)
            size = int(self.headers.get("Content-Length", "0"))
            if not 1 <= size <= 262144:
                return self.reply(413, b'{}')
            body = self.rfile.read(size)
            signature = "sha256=" + hmac.new(SECRET, body, hashlib.sha256).hexdigest()
            supplied = self.headers.get("X-Goldbach-Signature", "").encode()
            if not hmac.compare_digest(signature.encode(), supplied):
                return self.reply(401, b'{}')
            record = json.loads(body)
            lemma = record["lemma_id"]
            verdict = record["verdict"]
            run_id = record["run_id"]
            attempt = record["run_attempt"]
            manifest = record["manifest"]
            if type(run_id) is not int or run_id < 1 or type(attempt) is not int or attempt < 1:
                raise ValueError()
            if isinstance(lemma, str) and lemma in GAP_DESKS:
                desk = DESKS[GAP_DESKS[lemma]]
            elif not isinstance(lemma, str) or not re.fullmatch(r"L-goldbach-[a-z0-9-]+", lemma):
                raise ValueError()
            if verdict not in {"ACCEPTED", "REJECTED"}:
                raise ValueError()
            if verdict == "ACCEPTED":
                if not manifest["rests_on"]:
                    raise ValueError()
                for key in ("rests_on", "defs"):
                    if not isinstance(manifest[key], list):
                        raise ValueError()
                    for entry in manifest[key]:
                        if not isinstance(entry["module"], str) or not re.fullmatch(r"[a-f0-9]{64}", entry["sha256"]):
                            raise ValueError()
            elif manifest is not None:
                raise ValueError()
        except (ValueError, KeyError, TypeError, OSError):
            return self.reply(400, b'{}')
        with closing(sqlite3.connect(desk.db_path)) as conn, conn:
            if desk is not DESK and conn.execute(
                "SELECT 1 FROM goldbach_leases WHERE run_id = ? AND gap = ?", (run_id, lemma)
            ).fetchone() is None:
                return self.reply(409, b'{"error":"no matching authorized run"}')
            conn.execute("CREATE TABLE IF NOT EXISTS verdicts (run_id INTEGER, attempt INTEGER, body BLOB, PRIMARY KEY (run_id, attempt))")
            inserted = conn.execute("INSERT OR IGNORE INTO verdicts VALUES (?, ?, ?)", (run_id, attempt, body))
            if inserted.rowcount == 1:
                desk.record_verdict(record, conn)
        self.reply(200, b'{"status":"stored"}')

class Server(ThreadingHTTPServer):
    request_queue_size = 256

    def __init__(self, address, handler):
        self.tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.tls.load_cert_chain(CREDS / "fullchain.pem", CREDS / "privkey.pem")
        self.slots = BoundedSemaphore(16)
        super().__init__(address, handler)

    def process_request(self, request, address):
        self.slots.acquire()
        try:
            super().process_request(request, address)
        except BaseException:
            self.slots.release()
            raise

    def process_request_thread(self, request, address):
        try:
            super().process_request_thread(request, address)
        finally:
            self.slots.release()

    def finish_request(self, request, address):
        request.settimeout(8)
        with self.tls.wrap_socket(request, server_side=True) as connection:
            super().finish_request(connection, address)

if __name__ == "__main__":
    Server(("127.0.0.1", 8443), Handler).serve_forever()
