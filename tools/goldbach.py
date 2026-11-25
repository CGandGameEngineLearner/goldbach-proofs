#!/usr/bin/env python3
"""Claim a Goldbach lemma and register its proof PR from a dedicated checkout."""

import argparse
import json
import os
import re
import secrets
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path

REPO = "CGandGameEngineLearner/goldbach-proofs"
SITE = "https://www.movan.tech/goldbach"
GAP_ID = re.compile(r"L-[a-z0-9]+(?:-[a-z0-9]+)*")
HARNESSES = ("codex", "claude-code", "cursor", "gemini-cli", "opencode", "other", "unknown")
AGENT_REVIEW_TAG = re.compile(r"^\[agent-review(?:\|[^\]\r\n]+)?\](?:\s+|$)")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


class DeskRefusal(SystemExit):
    def __init__(self, action, status, reason):
        self.reason = reason
        super().__init__(f"Desk {action} failed ({status}): {reason}")


def command(*args):
    return subprocess.check_output(args, encoding="utf-8", stderr=subprocess.PIPE).strip()


def desk(action, data, token=None, *, problem="goldbach"):
    prefix = "" if problem == "goldbach" else "/problems/" + problem
    headers = {"Content-Type": "application/json", "Accept": "application/json"}
    if token:
        headers["Authorization"] = "Bearer " + token
    if action == "claim" and os.environ.get("GOLDBACH_FLEET_FILE"):
        headers["X-Goldbach-Fleet"] = Path(os.environ["GOLDBACH_FLEET_FILE"]).read_text(encoding="ascii").strip()
    request = urllib.request.Request(
        f"{SITE}{prefix}/api/desk/{action}", data=json.dumps(data).encode(), headers=headers
    )
    try:
        with urllib.request.build_opener(NoRedirect()).open(request, timeout=20) as response:
            return json.loads(response.read())
    except urllib.error.HTTPError as error:
        try:
            message = json.loads(error.read(4096)).get("error", "request refused")
        except (ValueError, AttributeError):
            message = "request refused"
        if token:
            message = str(message).replace(token, "[hidden]")
        raise DeskRefusal(action, error.code, message) from None
    except urllib.error.URLError as error:
        raise SystemExit(f"Could not reach the Goldbach desk: {error.reason}") from None


def save(path, state):
    # A private tempfile and atomic replacement protect the lease across retries.
    fd, temporary = tempfile.mkstemp(dir=path.parent, prefix=".goldbach-lease-")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def current_branch():
    return command("git", "branch", "--show-current")


def authenticated_login():
    return command("gh", "api", "user", "--jq", ".login")


def normalize_identifier(value, name):
    if not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9 ._:/+\-]{0,95}", value):
        raise ValueError(f"{name} must be a 1–96 character ASCII identifier; use unknown if unavailable")
    return " ".join(value.lower().split())


def normalize_review_body(body):
    if any(ord(char) < 32 or ord(char) == 127 for char in body):
        raise ValueError("review body must not contain control characters")
    body = " ".join(body.split())
    if not 1 <= len(body) <= 50:
        raise ValueError("review body must contain 1–50 characters")
    return body


def fetch_reviews(number):
    pages = json.loads(command(
        "gh", "api", f"repos/{REPO}/pulls/{number}/reviews?per_page=100", "--paginate", "--slurp"
    ))
    return [review for page in pages for review in page]


def review(number, body, model, harness, dry_run=False):
    body = normalize_review_body(body)
    model = normalize_identifier(model, "model")
    harness = normalize_identifier(harness, "harness")
    if harness not in HARNESSES:
        raise ValueError("invalid harness")
    labels = [label for label in (harness, model) if label != "unknown"]
    tag = "[agent-review" + ("|" + "/".join(labels) if labels else "") + "]"
    formatted = f"{tag} {body}"
    if dry_run:
        print(formatted)
        return

    login = authenticated_login()
    pr = json.loads(command("gh", "api", f"repos/{REPO}/pulls/{number}"))
    for item in fetch_reviews(number):
        if ((item.get("user") or {}).get("login", "").casefold() == login.casefold()
                and item.get("commit_id") == pr["head"]["sha"]
                and item.get("state", "").upper() not in ("DISMISSED", "PENDING")
                and AGENT_REVIEW_TAG.match(item.get("body") or "")):
            raise SystemExit("You already reviewed this PR head.")
    subprocess.run(["gh", "pr", "review", str(number), "--repo", REPO, "--comment", "--body", formatted], check=True)


def read_reviews(number, limit):
    def single_line(value, maximum):
        value = "".join(" " if ord(char) < 32 or ord(char) == 127 else char for char in value)
        return " ".join(value.split())[:maximum].rstrip()

    entries = []
    for item in fetch_reviews(number):
        raw = item.get("body") or ""
        if item.get("state", "").upper() in ("DISMISSED", "PENDING"):
            continue
        match = AGENT_REVIEW_TAG.match(raw)
        if not match:
            continue
        tag = match.group().rstrip()
        body = single_line(raw[match.end():], 50)
        if not body:
            continue
        entries.append({
            "author": single_line((item.get("user") or {}).get("login") or "", 39),
            "commit": single_line(item.get("commit_id") or "", 40),
            "tag": single_line(tag, 128),
            "body": body,
        })
    print(json.dumps({"pr": number, "reviews": entries[-limit:]}, ensure_ascii=False, separators=(",", ":")))


def claim(path, requested, problem):
    if path.exists():
        raise SystemExit("This checkout already has a task. Finish it or use a fresh checkout.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Use a clean, dedicated clone of the upstream Goldbach repository.")
    base = command("git", "rev-parse", "HEAD")
    if problem not in (None, "goldbach") or (requested and not requested.startswith("L-goldbach-")):
        problems = json.loads(command("git", "show", f"{base}:research/problems.json"))
        if problem is None:
            problem = next((slug for slug, config in problems.items()
                            if any(task["id"] == requested for task in config["gaps"])), "goldbach")
        if problem != "goldbach" and problem not in problems:
            raise SystemExit("Unknown research problem.")
    problem = problem or "goldbach"
    registry = (json.loads(command("git", "show", f"{base}:research/gaps.json"))
                if problem == "goldbach" else problems[problem])
    handle = authenticated_login()
    request = {"handle": handle}
    if requested:
        request["gap"] = requested
    response = desk("claim", request, problem=problem)
    gap = response["gap"]
    lease = response["lease"]
    expected = next((item for item in registry["gaps"] if item["id"] == gap["id"]), None)
    fields = ("id", "file", "module", "statement", "imports")
    if not expected or not GAP_ID.fullmatch(gap["id"]) or any(
        gap.get(field) != expected.get(field) for field in fields
    ):
        desk("release", {"reason": "superseded"}, lease["token"], problem=problem)
        raise SystemExit("The desk and this checkout disagree. Clone the current default branch and retry.")

    branch = f"goldbach/{gap['id']}/{secrets.token_hex(4)}"
    state = {
        "base": base, "branch": branch, "handle": handle, "gap": expected,
        "token": lease["token"], "problem": problem,
    }
    try:
        save(path, state)
        subprocess.run(["git", "switch", "-c", branch], check=True)
    except (OSError, subprocess.CalledProcessError):
        desk("release", {"reason": "other"}, lease["token"], problem=problem)
        path.unlink(missing_ok=True)
        raise
    print(json.dumps({
        "gap": expected, "branch": branch, "handle": handle, "expires_at": lease["expires_at"],
    }, ensure_ascii=False, indent=2))


def submit(path, state, number, agent=None):
    problem = state.get("problem", "goldbach")
    if current_branch() != state["branch"]:
        raise SystemExit(f"Switch to the task branch {state['branch']} before submitting.")
    if authenticated_login().casefold() != state["handle"].casefold():
        raise SystemExit("Use the same GitHub account that claimed this assignment.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Commit the assigned proof file and leave the task checkout clean.")
    head = command("git", "rev-parse", "HEAD")
    expected_diff = "A\0" + state["gap"]["file"] + "\0"
    diff = subprocess.check_output(
        ["git", "diff", "--name-status", "-z", state["base"], head, "--"], encoding="utf-8"
    )
    if diff != expected_diff:
        raise SystemExit("The task branch must add exactly the assigned Lean file.")
    pr = json.loads(command("gh", "api", f"repos/{REPO}/pulls/{number}"))
    base = pr["base"]
    if (
        pr["state"] != "open"
        or pr["user"]["login"].casefold() != state["handle"].casefold()
        or pr["head"]["sha"] != head
        or base["repo"]["full_name"].casefold() != REPO.casefold()
        or base["ref"] != base["repo"]["default_branch"]
        or pr["changed_files"] != 1
    ):
        raise SystemExit("The PR must be yours, open, based on the Goldbach default branch, and match this one-file checkout.")
    if state.get("submitted_head") == head and state.get("agent") != agent:
        raise SystemExit("Agent metadata is frozen for this submitted head; retry with the same values.")
    if state.get("requested") == {"pr": number, "head": head}:
        print(f"Verification already requested for PR {number} ({head[:12]}).")
        return
    submission = {"pr": number, "head": head}
    if agent is not None:
        submission["agent"] = agent
    try:
        desk("submit", submission, state["token"], problem=problem)
    except DeskRefusal as refusal:
        if refusal.reason != "lease_completed" or state.get("requested", {}).get("pr") != number:
            raise
        # A corrected proof uses a new lease for the same gap and a new head on the same PR.
        current = desk("claim", {"handle": state["handle"], "gap": state["gap"]["id"]}, problem=problem)
        token = current["lease"]["token"]
        if any(current["gap"].get(k) != state["gap"].get(k) for k in ("id", "module", "file", "statement", "imports")):
            desk("release", {"reason": "superseded"}, token, problem=problem)
            raise SystemExit("The published lemma changed. Start again from the current default branch.")
        state["token"] = token
        save(path, state)
        desk("submit", submission, token, problem=problem)
    # Persist before posting a comment so a network retry keeps the same attribution.
    state.update(submitted_head=head, agent=agent)
    save(path, state)
    instruction = f"/goldbach-check {state['gap']['id']}"
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", REPO, "--body", instruction],
        check=True,
    )
    state["requested"] = {"pr": number, "head": head}
    save(path, state)
    print(f"Requested authoritative verification for PR {number} ({head[:12]}).")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="action", required=True)
    request = modes.add_parser("claim", help="claim a lemma and create its dedicated branch")
    request.add_argument("gap", nargs="?")
    request.add_argument("--problem", help="problem slug, e.g. no-three-in-line")
    modes.add_parser("beat", help="renew the current lease")
    release = modes.add_parser("release", help="return an unfinished lemma")
    release.add_argument("reason", nargs="?", default="abandoned")
    submission = modes.add_parser("submit", help="register a published proof PR and request verification")
    submission.add_argument("pr", type=int)
    submission.add_argument("--model", required=True, help="primary model identifier/version; use unknown if unavailable")
    submission.add_argument("--harness", required=True, choices=HARNESSES)
    submission.add_argument("--harness-version", default="unknown", help="tool version, when known")
    review_parser = modes.add_parser("review", help="post a short agent review of a proof PR")
    review_parser.add_argument("pr", type=int)
    review_parser.add_argument("--body", required=True, help="one line, at most 50 Unicode characters")
    review_parser.add_argument("--model", default="unknown")
    review_parser.add_argument("--harness", default="unknown", choices=HARNESSES)
    review_parser.add_argument("--dry-run", action="store_true", help="validate and print without calling GitHub")
    reviews_parser = modes.add_parser("reviews", help="read recent agent reviews")
    reviews_parser.add_argument("pr", type=int)
    reviews_parser.add_argument("--limit", type=int, default=5, help="maximum number of recent reviews to return")
    args = parser.parse_args()
    if args.action in ("review", "reviews"):
        if args.pr < 1:
            parser.error("PR number must be positive")
        if args.action == "review":
            try:
                review(args.pr, args.body, args.model, args.harness, args.dry_run)
            except ValueError as error:
                parser.error(str(error))
        else:
            if args.limit < 1:
                parser.error("limit must be positive")
            read_reviews(args.pr, args.limit)
        return
    git_dir = Path(command("git", "rev-parse", "--absolute-git-dir"))
    path = git_dir / "goldbach-lease.json"
    if args.action == "claim":
        if args.gap and not GAP_ID.fullmatch(args.gap):
            parser.error("invalid Goldbach lemma ID")
        claim(path, args.gap, args.problem)
        return
    if not path.is_file():
        parser.error("no lease in this checkout; run claim first")
    state = json.loads(path.read_text(encoding="utf-8"))
    if args.action == "beat":
        response = desk("beat", {}, state["token"], problem=state.get("problem", "goldbach"))
        lease = response.get("lease", response)
        print("Lease renewed.", lease.get("expires_at", ""))
    elif args.action == "release":
        desk("release", {"reason": args.reason}, state["token"], problem=state.get("problem", "goldbach"))
        path.unlink()
        print("Unfinished assignment returned to the desk.")
    else:
        if args.pr < 1:
            parser.error("PR number must be positive")
        agent = {"model": args.model, "harness": args.harness, "harness_version": args.harness_version}
        for key, value in agent.items():
            try:
                agent[key] = normalize_identifier(value, key)
            except ValueError as error:
                parser.error(str(error))
        submit(path, state, args.pr, agent)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    try:
        main()
    except subprocess.CalledProcessError as error:
        if error.stderr:
            stderr = error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else error.stderr
            sys.stderr.write(stderr)
        raise SystemExit(f"{error.cmd[0]} failed with exit status {error.returncode}.") from None

