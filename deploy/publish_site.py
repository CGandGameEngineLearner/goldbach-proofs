"""Publish website PRs merged by authorized maintainers after CI verifies the exact commit."""
import argparse
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path
from urllib.request import Request, urlopen

REPO = "CGandGameEngineLearner/goldbach-proofs"
OWNER_ID = 103875245
STORE = Path("/opt/goldbach-site-releases")
APP = Path("/opt/goldbach-web")
CHECKPOINT = STORE / "checkpoint"
PENDING = STORE / "pending.json"
MARKER = ".site-revision"
HEALTH = ("https://www.goldbach.tech/health", "https://www.movan.tech/goldbach/health")
RUNTIME = re.compile(
    r"(?:[a-z][a-z0-9-]*\.(?:html|js|css|png|svg)|join(?:-zh)?\.txt|china-apnic\.txt|"
    r"(?:server|desk|presence|landau|github_identity|zhihu_oauth|sponsors)\.py)"
)


def git(*args):
    return subprocess.check_output(["git", "--git-dir", str(STORE / "git"), *args], timeout=70)


def atomic(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, "wb") as staged:
            staged.write(data)
            staged.flush()
            os.fsync(staged.fileno())
        temporary.chmod(0o644)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def api(path):
    request = Request("https://api.github.com/repos/" + REPO + path,
                      headers={"Accept": "application/vnd.github+json"})
    with urlopen(request, timeout=12) as reply:
        return json.load(reply)


def verified(sha):
    prs = api(f"/commits/{sha}/pulls")
    pr = next((p for p in prs if p.get("merge_commit_sha") == sha
               and p["base"]["ref"] == "main" and p["base"]["repo"]["full_name"] == REPO
               and p.get("merged_at")), None)
    if pr is None:
        raise RuntimeError(f"Website changes at {sha} require a merged PR")
    detail = api(f'/pulls/{pr["number"]}')
    allowed = {OWNER_ID, *(int(uid) for uid in os.environ.get("GOLDBACH_SITE_RELEASE_MERGER_IDS", "").split())}
    if (detail.get("merged_by") or {}).get("id") not in allowed:
        raise RuntimeError(f'PR #{pr["number"]} requires an authorized website publisher')
    runs = api("/actions/workflows/site-release.yml/runs?event=push&branch=main&head_sha=" + sha)["workflow_runs"]
    return any(run["head_sha"] == sha and run["conclusion"] == "success" for run in runs)


def restart(expected):
    subprocess.run(["systemctl", "restart", "goldbach-web"], check=True, timeout=30)
    for _ in range(10):
        try:
            for url in HEALTH:
                with urlopen(url, timeout=4) as response:
                    health = json.load(response)
                if health.get("status") != "ok" or health.get("site_revision") != expected:
                    break
            else:
                return
        except (OSError, ValueError):
            pass
        time.sleep(1)
    raise RuntimeError(f"Public health did not confirm website revision {expected}")


def blob(commit, name):
    path = "deploy/" + name
    entry = git("ls-tree", commit, "--", path)
    if not entry:
        return None
    if not entry.startswith((b"100644 blob ", b"100755 blob ")):
        raise ValueError(f"Expected a regular Git file for {path}")
    return git("show", f"{commit}:{path}")


def restore(backup, files):
    for name in files:
        old = backup / name
        target = APP / name
        if old.exists():
            atomic(target, old.read_bytes())
        else:
            target.unlink(missing_ok=True)
    marker = backup / MARKER
    restart(marker.read_text().strip() if marker.exists() else None)


def activate(sha, files):
    old = {}
    updates = {}
    for name in files:
        target = APP / name
        if target.is_symlink():
            raise RuntimeError(f"Unexpected symlink at {name}")
        live = target.read_bytes() if target.exists() else None
        base, candidate = blob(sha + "^1", name), blob(sha, name)
        if live != base and live != candidate:
            raise RuntimeError(f"Live file differs from both Git versions: {name}")
        old[name] = live
        updates[name] = candidate
    marker = APP / MARKER
    old[MARKER] = marker.read_bytes() if marker.exists() else None
    updates[MARKER] = (sha + "\n").encode()

    backup = Path(tempfile.mkdtemp(prefix=sha[:12] + "-", dir=STORE))
    for name, value in old.items():
        if value is not None:
            atomic(backup / name, value)
    atomic(PENDING, json.dumps({"sha": sha, "backup": str(backup), "files": list(old)}).encode())
    try:
        for name, value in updates.items():
            if value is None:
                (APP / name).unlink(missing_ok=True)
            else:
                atomic(APP / name, value)
        restart(sha)
        atomic(CHECKPOINT, sha.encode())
    except Exception:
        restore(backup, old)
        PENDING.unlink()
        raise
    PENDING.unlink()
    print(f"Published website {sha}; rollback snapshot {backup}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bootstrap", metavar="LIVE_BASE_SHA")
    args = parser.parse_args()
    if PENDING.exists():
        interrupted = json.loads(PENDING.read_bytes())
        if not CHECKPOINT.exists() or CHECKPOINT.read_text().strip() != interrupted["sha"]:
            restore(Path(interrupted["backup"]), interrupted["files"])
        PENDING.unlink()
    if not (STORE / "git").exists():
        subprocess.run(["git", "init", "--bare", str(STORE / "git")], check=True)
    git("fetch", "--quiet", "https://github.com/" + REPO + ".git", "refs/heads/main")
    if args.bootstrap:
        if CHECKPOINT.exists() or not re.fullmatch(r"[a-f0-9]{40}", args.bootstrap):
            parser.error("bootstrap requires a fresh store and a full baseline SHA")
        git("merge-base", "--is-ancestor", args.bootstrap, "FETCH_HEAD")
        atomic(CHECKPOINT, args.bootstrap.encode())
        print(f"Recorded website baseline {args.bootstrap}", flush=True)
        return
    baseline = CHECKPOINT.read_text().strip()
    git("merge-base", "--is-ancestor", baseline, "FETCH_HEAD")
    for sha in git("rev-list", "--first-parent", "--reverse", baseline + "..FETCH_HEAD").decode().splitlines():
        changed = git("diff", "--no-renames", "--name-only", "-z", sha + "^1", sha, "--", "deploy/").decode().split("\0")
        files = [p.removeprefix("deploy/") for p in changed if RUNTIME.fullmatch(p.removeprefix("deploy/"))]
        if not files:
            atomic(CHECKPOINT, sha.encode())
        elif verified(sha):
            activate(sha, files)
        else:
            print(f"Waiting for successful website verification for {sha}", flush=True)
            return


if __name__ == "__main__":
    main()
