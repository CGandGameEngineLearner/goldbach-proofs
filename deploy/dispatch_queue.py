import datetime
import hashlib
import hmac
import json
import os
from pathlib import Path
import re
import urllib.error
import urllib.parse
import urllib.request

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None

opener = urllib.request.build_opener(NoRedirect())

def fetch(url, body, headers, label, maximum=65536):
    request = urllib.request.Request(url, body, {
        "Content-Type": "application/json",
        **headers,
    })
    try:
        with opener.open(request, timeout=15) as response:
            data = response.read(maximum + 1)
            if len(data) > maximum:
                raise SystemExit(f"{label} response exceeds size limit")
            return data
    except urllib.error.HTTPError as error:
        if body is None and error.code in (404, 410):
            return b"null"
        raise SystemExit(f"{label} returned HTTP {error.code}") from None
    except urllib.error.URLError:
        raise SystemExit(f"{label} could not be reached") from None

env = dict(os.environ)
if credentials := env.get("CREDENTIALS_DIRECTORY"):
    directory = Path(credentials)
    env["DESK_SECRET"] = (directory / "webhook").read_text().strip()
    env["GH_TOKEN"] = (directory / "github-token").read_text().strip()
if not env.get("GH_TOKEN"):
    raise SystemExit("GitHub Actions dispatch credential required")
desk = urllib.parse.urlsplit(env["DESK_URL"])
if (desk.scheme != "https" or not desk.hostname or desk.username is not None
        or desk.query or desk.fragment or not env["DESK_SECRET"] or not env["DEFAULT_BRANCH"]):
    raise SystemExit("HTTPS desk URL, signing secret and default branch required")
request_body = b"{}"
signature = hmac.new(env["DESK_SECRET"].encode(), request_body, hashlib.sha256).hexdigest()
response = fetch(
    desk.geturl().rstrip("/") + "/pending",
    request_body,
    {"X-Goldbach-Signature": "sha256=" + signature, "Accept": "application/json"},
    "Desk queue",
)
rows = json.loads(response)["pending"]
if not isinstance(rows, list) or len(rows) > 16:
    raise SystemExit("Invalid desk batch")

pending = []
for row in rows:
    if not isinstance(row, dict):
        raise SystemExit("Invalid queued proof")
    pr, gap, head, handle = (row.get(field) for field in ("pr", "gap", "head", "handle"))
    if (type(pr) is not int or not 1 <= pr <= 9999999
            or not isinstance(gap, str) or not re.fullmatch(r"L-[a-z0-9]+(?:-[a-z0-9]+)*", gap)
            or len(gap) > 64 or not isinstance(head, str) or not re.fullmatch(r"[a-f0-9]{40}", head)
            or not isinstance(handle, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}", handle)):
        raise SystemExit("Invalid queued proof")
    pending.append((pr, gap, head, handle))

api = f"https://api.github.com/repos/{env['REPO']}"
github_headers = {
    "Authorization": f"Bearer {env['GH_TOKEN']}",
    "Accept": "application/vnd.github+json",
    "X-GitHub-Api-Version": "2022-11-28",
}

def github(path):
    return json.loads(fetch(api + path, None, github_headers, "GitHub", maximum=2097152))

def matching_author_comment(pr, handle, gap):
    since = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=1)
    for page in range(1, 4):
        query = urllib.parse.urlencode({
            "per_page": 100, "page": page, "since": since.isoformat(timespec="seconds"),
        })
        comments = github(f"/issues/{pr}/comments?{query}")
        if not comments:
            return False
        if any(
            (comment.get("user") or {}).get("login", "").casefold() == handle.casefold()
            and comment.get("body", "").strip() == f"/goldbach-check {gap}"
            for comment in comments
        ):
            return True
        if len(comments) < 100:
            return False
    return False

dispatched = set()
for pr, gap, head, handle in pending:
    if pr in dispatched:
        continue
    pull = github(f"/pulls/{pr}")
    if (not pull or pull["state"] != "open" or pull["changed_files"] != 1
            or pull["base"]["ref"] != env["DEFAULT_BRANCH"] or pull["head"]["sha"] != head
            or (pull.get("user") or {}).get("login", "").casefold() != handle.casefold()
            or not matching_author_comment(pr, handle, gap)):
        print(f"Skipped PR {pr}: current PR and author request not yet verified")
        continue
    body = json.dumps({
        "ref": env["DEFAULT_BRANCH"],
        "inputs": {"pr": str(pr), "gap": gap, "desk": True},
    }).encode()
    fetch(api + "/actions/workflows/authoritative.yml/dispatches", body,
          github_headers, "Authoritative dispatch")
    dispatched.add(pr)
    print(f"Dispatched PR {pr} for {gap}")
if not pending:
    print("No queued proofs")
