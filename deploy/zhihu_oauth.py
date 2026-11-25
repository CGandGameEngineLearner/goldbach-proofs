"""Opt-in Zhihu attribution. Provider tokens never enter persistent storage."""

import hashlib
import hmac
import http.client
import json
import os
import re
import secrets
import sqlite3
import time
from contextlib import closing
from html import escape
from http.cookies import CookieError, SimpleCookie
from urllib.parse import urlencode
from urllib.request import HTTPRedirectHandler, Request, build_opener

from github_identity import GithubProofError, PROOF_FILENAME, new_challenge, proof_text, verify_gist
import sponsors


ORIGIN = "https://www.goldbach.tech"
BASE = "/auth/zhihu"
CALLBACK = ORIGIN + BASE + "/callback"
COOKIE = "__Host-goldbach-zhihu"
LIFETIME = 1200


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None


def provider_json(request):
    with build_opener(NoRedirect()).open(request, timeout=8) as response:
        raw = response.read(65537)
    if len(raw) > 65536:
        raise ValueError("oversize provider reply")
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError("invalid provider reply")
    return data


def exchange_profile(config, code):
    form = urlencode({**config, "grant_type": "authorization_code", "redirect_uri": CALLBACK, "code": code})
    token = provider_json(Request("https://openapi.zhihu.com/access_token", data=form.encode(),
                                  headers={"Content-Type": "application/x-www-form-urlencoded"})).get("access_token")
    if not isinstance(token, str) or not re.fullmatch(r"[!-~]{1,8192}", token):
        raise ValueError("token exchange failed")
    profile = provider_json(Request("https://openapi.zhihu.com/user", headers={"Authorization": "Bearer " + token}))
    uid, name = profile.get("uid"), profile.get("fullname")
    if not re.fullmatch(r"[1-9][0-9]{0,19}", str(uid)) or not isinstance(name, str) or not 0 < len(name.strip()) <= 160:
        raise ValueError("basic identity unavailable")
    avatar = profile.get("avatar_path")
    if not isinstance(avatar, str) or not re.fullmatch(r"https://(?:[a-zA-Z0-9-]+\.)*zhimg\.com/[^\s\\]{1,1900}", avatar):
        avatar = ""
    slug = profile.get("url_token")
    link = "https://www.zhihu.com/people/" + slug if isinstance(slug, str) and re.fullmatch(r"[\w-]{1,120}", slug) else ""
    return {"subject": str(uid), "name": name.strip(), "avatar_url": avatar, "profile_url": link}


def digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


def page(status, title, content, lang="zh"):
    html = (f'<!doctype html><html lang="{lang}"><meta charset="utf-8"><meta name="viewport" '
            f'content="width=device-width,initial-scale=1"><title>{title}</title>'
            '<style>body{max-width:38rem;margin:10vh auto;padding:0 1rem;font:18px/1.65 system-ui;color:#203a30;'
            'background:#faf8f2}h1{line-height:1.2}input:not([type=checkbox]),button{font:inherit;padding:.4rem;'
            'margin:.4rem 0;max-width:95%}button{cursor:pointer}pre{white-space:pre-wrap;overflow-wrap:anywhere;'
            'padding:.8em;background:white}a{color:#235642}label{display:block}</style>'
            f'<main><h1>{title}</h1>{content}</main></html>')
    return status, {"Content-Type": "text/html; charset=utf-8"}, html.encode()


def redirect(url, cookie=None):
    headers = {"Location": url}
    if cookie:
        headers["Set-Cookie"] = f"{COOKIE}={cookie}; Path=/; Secure; HttpOnly; SameSite=Lax; Max-Age={LIFETIME}"
    return 303, headers, b""


class ZhihuOAuth:
    def __init__(self, db_path, config):
        self.db = db_path
        self.config = {k: config[k] for k in ("app_id", "app_key")} if config else None
        with closing(sqlite3.connect(self.db)) as db:
            db.executescript("""
                CREATE TABLE IF NOT EXISTS sessions (
                    sid TEXT PRIMARY KEY, csrf TEXT NOT NULL, lang TEXT NOT NULL, expires INTEGER NOT NULL,
                    state TEXT, subject TEXT, profile TEXT, handle TEXT, challenge TEXT);
                CREATE INDEX IF NOT EXISTS expiry ON sessions(expires);
                CREATE TABLE IF NOT EXISTS links (
                    subject TEXT PRIMARY KEY, github_id INTEGER UNIQUE NOT NULL, handle TEXT UNIQUE NOT NULL,
                    name TEXT NOT NULL, avatar_url TEXT NOT NULL, profile_url TEXT NOT NULL);
            """)
            sponsors.setup(db)

    def public_profiles(self, handles=None):
        if handles is not None and not handles:
            return {}
        with closing(sqlite3.connect(self.db)) as db:
            db.row_factory = sqlite3.Row
            result = {}
            # Stay below SQLite's variable limit even for large all-time rankings.
            batches = [None] if handles is None else [handles[i:i+400] for i in range(0, len(handles), 400)]
            for batch in batches:
                where = "" if batch is None else " WHERE handle IN (" + ",".join("?" for _ in batch) + ")"
                for row in db.execute("SELECT handle,name,avatar_url,profile_url FROM links" + where, batch or ()):
                    result[row["handle"]] = {k: row[k] for k in ("name", "avatar_url", "profile_url")}
            return result

    def session(self, db, lang, profile=None):
        token = secrets.token_urlsafe(32)
        db.execute("DELETE FROM sessions WHERE expires <= ?", (int(time.time()),))
        db.execute("INSERT INTO sessions(sid,csrf,lang,expires,subject,profile) VALUES(?,?,?,?,?,?)",
                   (digest(token), secrets.token_urlsafe(32), lang, int(time.time()) + LIFETIME,
                    profile["subject"] if profile else None, json.dumps(profile) if profile else None))
        return token

    @staticmethod
    def session_id(headers):
        cookies = SimpleCookie()
        try:
            cookies.load(headers.get("Cookie", ""))
        except CookieError:
            return ""
        cookie = cookies.get(COOKIE)
        return digest(cookie.value) if cookie else ""

    def account_link(self, headers, lang):
        zh = lang == "zh"
        url = f"{ORIGIN}{sponsors.DESK}?lang={lang}"
        sid = self.session_id(headers) if headers.get("Host","").lower() in ("www.goldbach.tech","www.goldbach.tech:443") else ""
        if sid:
            with closing(sqlite3.connect(self.db)) as db:
                record = db.execute("SELECT profile FROM sessions WHERE sid=? AND expires>? AND subject IS NOT NULL",
                                    (sid,int(time.time()))).fetchone()
            if record:
                profile = json.loads(record[0])
                name = escape(profile["name"])
                avatar = (f'<img referrerpolicy="no-referrer" src="{escape(profile["avatar_url"])}" width="30" height="30" alt="">' if profile["avatar_url"]
                          else f'<b aria-hidden="true">{escape(profile["name"][:1])}</b>')
                return f'<a class="account-link" href="{url}" title="{name}">{avatar}{"设置" if zh else "Settings"}</a>'
        return f'<a class="account-link" href="{url}&amp;entry=home">{"知乎登录" if zh else "Zhihu login"}</a>'

    def can_upload_sponsor(self, headers):
        if not self.config or headers.get("Host", "").lower() not in ("www.goldbach.tech", "www.goldbach.tech:443"):
            return False
        sid = self.session_id(headers)
        if not sid:
            return False
        with closing(sqlite3.connect(self.db, timeout=5)) as db:
            return db.execute("SELECT 1 FROM sessions WHERE sid=? AND expires>? AND subject IS NOT NULL",
                              (sid, int(time.time()))).fetchone() is not None

    def handle(self, method, path, params, headers):
        lang = "en" if params.get("lang") == "en" else "zh"
        canonical = headers.get("Host", "").lower() in ("www.goldbach.tech", "www.goldbach.tech:443")
        if not canonical:
            if method == "GET" and path == BASE:
                text = ("Continue on the registered callback domain" if lang == "en" else "前往已登记的回调域名")
                info = ("Binding requires access to www.goldbach.tech." if lang == "en" else "绑定需要能访问 www.goldbach.tech。")
                return page(200, "Zhihu · GitHub", f'<p>{info}</p><a href="{ORIGIN}{BASE}?lang={lang}">{text}</a>', lang)
            return page(400, "Invalid callback host", "")
        if not self.config:
            return page(503, "OAuth unavailable", "")
        sid = self.session_id(headers)
        with closing(sqlite3.connect(self.db, timeout=5)) as db, db:
            db.row_factory = sqlite3.Row
            row = db.execute("SELECT * FROM sessions WHERE sid=? AND expires>?", (sid, int(time.time()))).fetchone()
            if row:
                lang = row["lang"]
            def err(status, zh, en):
                return page(status, en if lang == "en" else zh, f'<a href="{BASE}?lang={lang}">返回 / Return</a>', lang)
            if path == sponsors.DESK or path.startswith(sponsors.DESK + "/"):
                fresh = None
                if not row:
                    if method == "POST" and path == sponsors.DESK + "/upload":
                        message = "Your session expired. Sign in with Zhihu and retry." if lang == "en" else "登录已过期，请重新登录知乎后提交。"
                        return sponsors.upload_notice(403, lang, message)
                    if method != "GET" or path != sponsors.DESK:
                        return err(403, "请先登录知乎", "Sign in with Zhihu")
                    fresh = self.session(db, lang)
                    row = db.execute("SELECT * FROM sessions WHERE sid=?", (digest(fresh),)).fetchone()
                result = sponsors.handle(method,path,params,headers,db,row,lang,redirect)
                if fresh:
                    result[1]["Set-Cookie"] = redirect(BASE, fresh)[1]["Set-Cookie"]
                return result
            if method == "GET" and path == BASE:
                fresh = None
                if not row:
                    fresh = self.session(db, lang)
                    row = db.execute("SELECT * FROM sessions WHERE sid=?", (digest(fresh),)).fetchone()
                response = self.management(db, row)
                if fresh:
                    response[1].update({"Set-Cookie": redirect(BASE, fresh)[1]["Set-Cookie"]})
                return response
            if method == "GET" and path == BASE + "/callback":
                state, code = params.get("state", ""), params.get("authorization_code", "")
                if not (row and row["state"] and hmac.compare_digest(digest(state), row["state"].split(":")[-1])):
                    return err(400, "授权未能关联到本次浏览器会话", "Authorization did not match this browser session")
                if not db.execute("UPDATE sessions SET state=NULL WHERE sid=? AND state=?", (sid, row["state"])).rowcount:
                    return err(400, "授权请求已使用", "Authorization already used")
                db.commit()
                if not code or len(code) > 4096 or "error" in params:
                    return err(400, "知乎授权未完成", "Zhihu authorization was not completed")
                try:
                    profile = exchange_profile(self.config, code)
                except (OSError, ValueError, http.client.HTTPException, RecursionError):
                    return err(502, "知乎未返回可用于绑定的基础身份", "Zhihu did not return a usable basic identity")
                db.execute("DELETE FROM sessions WHERE sid=?", (sid,))
                sponsors.bootstrap(db, profile, os.environ.get("GOLDBACH_INITIAL_ADMIN_PROFILE"),
                                   os.environ.get("GOLDBACH_INITIAL_ADMIN_UID"))
                dest = {"s": sponsors.DESK, "h": "/?lang="+lang}.get(row["state"].split(":")[0],BASE)
                return redirect(dest, self.session(db, lang, profile))
            if method != "POST" or path not in (BASE+"/start", BASE+"/challenge", BASE+"/bind", BASE+"/unlink"):
                return err(404, "此页面不存在", "Page not found")
            if (not row or headers.get("Origin") != ORIGIN or
                    not hmac.compare_digest(digest(params.get("csrf", "")), digest(row["csrf"]))):
                return err(403, "请重新打开绑定页面", "Reopen the account linking page")
            if path.endswith("/start"):
                token = secrets.token_urlsafe(32)
                prefix = {"sponsors":"s:", "home":"h:"}.get(params.get("next"), "")
                db.execute("UPDATE sessions SET state=? WHERE sid=?", (prefix + digest(token), sid))
                query = urlencode({"app_id": self.config["app_id"], "redirect_uri": CALLBACK,
                                   "response_type": "code", "state": token})
                return redirect("https://openapi.zhihu.com/authorize?" + query)
            if not row["subject"]:
                return err(403, "请先授权知乎", "Authorize Zhihu first")
            if path.endswith("/unlink"):
                db.execute("DELETE FROM links WHERE subject=?", (row["subject"],))
                db.execute("DELETE FROM sessions WHERE subject=?", (row["subject"],))
                return redirect(BASE+"?lang="+lang)
            try:
                if path.endswith("/challenge"):
                    challenge, handle = new_challenge(), params.get("handle", "").strip().lower()
                    proof_text(challenge, handle)
                    db.execute("UPDATE sessions SET challenge=?,handle=? WHERE sid=?", (challenge, handle, sid))
                    return redirect(BASE)
                if params.get("public") != "yes" or not row["challenge"]:
                    return err(400, "请验证 GitHub 并明确同意公开署名", "Verify GitHub and opt in to public attribution")
                gid, login = verify_gist(params.get("gist", ""), row["challenge"], row["handle"])
            except GithubProofError as exc:
                return err(exc.status, "GitHub 验证未完成，请核对账号及 Gist 后重试", "GitHub verification failed; check the account and gist")
            if not db.execute("UPDATE sessions SET challenge=NULL WHERE sid=? AND challenge=? AND expires>?",
                              (sid, row["challenge"], int(time.time()))).rowcount:
                return err(409, "验证请求已失效", "Verification expired")
            p = json.loads(row["profile"])
            try:
                db.execute("""INSERT INTO links VALUES(?,?,?,?,?,?)
                              ON CONFLICT(subject) DO UPDATE SET name=excluded.name,
                              handle=excluded.handle,avatar_url=excluded.avatar_url,profile_url=excluded.profile_url
                              WHERE links.github_id=excluded.github_id""",
                           (row["subject"], gid, login, p["name"], p["avatar_url"], p["profile_url"]))
                if not db.execute("SELECT changes()").fetchone()[0]:
                    raise sqlite3.IntegrityError("different linked account")
            except sqlite3.IntegrityError:
                return err(409, "账号已有绑定，请先解除原绑定", "Unlink the existing account first")
            return redirect(BASE)

    @staticmethod
    def management(db, row):
        en = row["lang"] == "en"
        def tr(zh, english):
            return english if en else zh
        def form(action, fields, submit):
            return (f'<form method="post" action="{BASE}/{action}"><input type="hidden" name="csrf" '
                    f'value="{row["csrf"]}">{fields}<button>{submit}</button></form>')
        title = tr("知乎贡献者署名", "Zhihu contributor attribution")
        info = tr("你可以把知乎署名加到自己的 GitHub 贡献记录上。", "Add your Zhihu identity to your GitHub contribution record.")
        body = f'<p>{info}</p>'
        if not row["subject"]:
            body += form("start", "", tr("使用知乎授权", "Authorize with Zhihu"))
        else:
            name = escape(json.loads(row["profile"])["name"])
            body += '<p>' + tr("当前知乎账号", "Zhihu account") + f' · <strong>{name}</strong></p>'
            linked = db.execute("SELECT handle FROM links WHERE subject=?", (row["subject"],)).fetchone()
            if linked:
                body += f'<p>GitHub · @{escape(linked["handle"])}</p>'
                body += form("unlink", "", tr("解除绑定并撤下知乎署名", "Unlink and remove public attribution"))
            else:
                body += form("challenge", '<label>GitHub <input name="handle" maxlength="39" required></label>',
                             tr("生成账号验证文本", "Generate account verification text"))
                if row["challenge"]:
                    instructions = tr("用自己的 GitHub 账号创建一个 Gist，按下方文件名和内容保存，再粘贴该 Gist 的地址。",
                                      "Create a gist with your GitHub account using the filename and contents below, then paste its URL.")
                    body += (f'<p>{instructions}</p><a href="https://gist.github.com/" target="_blank" rel="noreferrer">GitHub Gist</a>'
                             f'<p><code>{PROOF_FILENAME}</code></p><pre>{escape(proof_text(row["challenge"],row["handle"]))}</pre>')
                    label = tr("同意在公开贡献榜上展示我的知乎昵称、头像及可用的主页链接。",
                               "Show my Zhihu name, avatar and available profile link on the public leaderboard.")
                    body += form("bind", '<label>Gist URL <input name="gist" required></label>'
                                 f'<label><input type="checkbox" name="public" value="yes" required> {label}</label>',
                                 tr("验证并公开署名", "Verify and publish attribution"))
        body += f'<p><a href="/?lang={row["lang"]}#rankings">' + tr("返回贡献榜", "Back to leaderboard") + '</a></p>'
        return page(200, title, body, row["lang"])
