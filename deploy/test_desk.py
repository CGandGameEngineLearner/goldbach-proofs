import hashlib
import hmac
import json
import sqlite3
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from contextlib import closing
from pathlib import Path
from unittest.mock import patch

from deploy.desk import Desk, LEASE_SECONDS, MAX_RESEARCH_SECONDS

GAPS = [
    {"id": f"L-goldbach-{i:03}", "statement": f"True {-i}"}
    for i in range(1, 6)
]
SECRET = b"test-secret"
BASE = "/api/desk/"
START = 1_000_000


class DeskTests(unittest.TestCase):
    def setUp(self):
        folder = self.enterContext(tempfile.TemporaryDirectory())
        self.db = Path(folder) / "verdicts.sqlite3"
        self.desk = Desk(self.db, GAPS, SECRET)

    def test_challenges_require_explicit_claim(self):
        self.desk.gaps = {g["id"]: {**g, "challenge_only": True} for g in GAPS}
        automatic = {"handle": "alice"}
        self.assertEqual(self.request("claim", automatic)[0], 409)
        self.desk.gaps[GAPS[2]["id"]]["challenge_only"] = False
        code, result = self.request("claim", automatic)
        self.assertEqual(code, 201)
        self.assertEqual(result["gap"]["id"], GAPS[2]["id"])
        self.assertEqual(self.request("claim", {"handle": "bob", "gap": GAPS[0]["id"]})[0], 201)

    def request(self, path, body, *, token=None, sign=False, now=START, ip="2001:db8::1"):
        content = json.dumps(body, separators=(",", ":")).encode()
        headers = {}
        if token is not None:
            headers["Authorization"] = "Bearer " + token
        if sign:
            headers["X-Goldbach-Signature"] = "sha256=" + hmac.new(SECRET, content, hashlib.sha256).hexdigest()
        with patch("deploy.desk.time.time", return_value=now):
            return self.desk.dispatch(BASE + path, body, headers, ip, content)

    def claim(self, handle="Alice", **options):
        status, data = self.request("claim", {"handle": handle, "gap": GAPS[0]["id"]}, **options)
        self.assertEqual(status, 201, data)
        return data["lease"]["token"]

    def submit(self, token, *, pr=8, head="a" * 40):
        return self.request("submit", {"pr": pr, "head": head, "agent": {"model": "test-model", "harness": "codex"}}, token=token)

    def authorization(self, **changes):
        result = {
            "pr": 8,
            "head": "a" * 40,
            "handle": "Alice",
            "gap": GAPS[0]["id"],
            "run_id": 102,
            "statement_sha256": hashlib.sha256(GAPS[0]["statement"].encode()).hexdigest(),
        }
        result.update(changes)
        return result

    def record(self, run_id, lemma_id, verdict, attempt=1):
        data = {"run_id": run_id, "lemma_id": lemma_id, "verdict": verdict, "run_attempt": attempt}
        with closing(sqlite3.connect(self.db)) as conn, conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS verdicts (
                    run_id INTEGER, attempt INTEGER, body BLOB, PRIMARY KEY (run_id, attempt)
                )
            """)
            conn.execute("INSERT INTO verdicts VALUES (?, ?, ?)", (run_id, attempt, json.dumps(data).encode()))
            self.desk.record_verdict(data, conn)

    def status(self, now=START):
        with patch("deploy.desk.time.time", return_value=now):
            return self.desk.public_status()

    def test_pending_pr_keeps_authorization_while_next_task_is_claimed(self):
        first = self.claim()
        self.assertEqual(self.submit(first)[0], 200)
        status, second = self.request("claim", {"handle": "Alice"})
        self.assertEqual(status, 201)
        self.assertNotEqual(second["gap"]["id"], GAPS[0]["id"])
        self.assertEqual(self.request("claim", {"handle": "Alice"})[0], 409)
        self.assertEqual(self.submit(second["lease"]["token"], pr=9, head="b"*40)[0], 200)
        self.assertEqual(self.request("claim", {"handle": "Alice"})[0], 409)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)

    def test_pending_is_private_and_lists_submitted_unchecked_lease(self):
        self.assertEqual(self.request("pending", {})[0], 401)
        token = self.claim()
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "working"})
        self.assertEqual(self.request("pending", {}, sign=True)[1], {"pending": []})
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "submitted"})
        self.assertEqual(self.request("pending", {}, sign=True)[1], {"pending": [
            {"pr": 8, "head": "a" * 40, "handle": "alice", "gap": GAPS[0]["id"]}
        ]})
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "checking"})
        self.assertEqual(self.request("pending", {}, sign=True)[1], {"pending": []})

    def test_prior_proofs_are_ineligible_and_uncredited(self):
        self.record(99, GAPS[0]["id"], "ACCEPTED")
        self.assertEqual(self.request("claim", {"handle": "Bob", "gap": GAPS[0]["id"]})[0], 409)
        self.assertEqual(self.request("claim", {"handle": "Bob"})[1]["gap"]["id"], GAPS[1]["id"])
        self.assertEqual(self.status()["leaderboard"], [])

    def test_only_one_participant_can_claim_the_same_gap_concurrently(self):
        def claim(i):
            return self.desk.claim({"handle": f"Agent{i}", "gap": GAPS[0]["id"]}, f"192.0.2.{i}", START)[0]

        with ThreadPoolExecutor(max_workers=8) as workers:
            outcomes = list(workers.map(claim, range(1, 17)))
        self.assertEqual(outcomes.count(201), 1)
        self.assertEqual(outcomes.count(409), 15)

    def test_expiry_and_release(self):
        token = self.claim()
        with self.desk.transaction(write=True) as conn:
            conn.execute("UPDATE goldbach_leases SET expires_at = ?", (START + MAX_RESEARCH_SECONDS,))
        almost_absolute = START + MAX_RESEARCH_SECONDS - 120
        status, data = self.request("beat", {}, token=token, now=almost_absolute)
        self.assertEqual(status, 200)
        self.assertEqual(data["expires_at"], START + MAX_RESEARCH_SECONDS)
        self.assertEqual(self.request("beat", {}, token=token, now=START + MAX_RESEARCH_SECONDS)[0], 410)
        self.assertEqual(self.status(START + MAX_RESEARCH_SECONDS)["activities"][0]["kind"], "expired")
        replacement = self.claim("Bob", now=START + MAX_RESEARCH_SECONDS)
        self.assertEqual(self.request("release", {}, token=replacement, now=START + MAX_RESEARCH_SECONDS)[0], 200)
        self.assertEqual(self.status(START + MAX_RESEARCH_SECONDS)["active"], 0)

    def test_only_a_matching_signed_workflow_can_authorize(self):
        token = self.claim()
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.request("authorize", self.authorization())[0], 401)
        for changes in (
            {"head": "b" * 40},
            {"handle": "Mallory"},
            {"statement_sha256": "0" * 64},
            {"pr": 9},
        ):
            self.assertEqual(self.request("authorize", self.authorization(**changes), sign=True)[0], 409)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True), (200, {"authorized": True}))
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.assertEqual(self.request("authorize", self.authorization(run_id=103), sign=True)[0], 409)
        self.assertEqual(self.request("release", {}, token=token)[0], 409)

    def test_unverified_submission_cannot_poison_a_pr_head(self):
        other_status, other = self.request("claim", {"handle": "Mallory", "gap": GAPS[1]["id"]})
        self.assertEqual(other_status, 201)
        self.assertEqual(self.submit(other["lease"]["token"])[0], 200)
        self.assertEqual(self.submit(self.claim())[0], 200)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)

    def test_only_matching_verdict_releases_lease_and_credits_verified_author(self):
        token = self.claim()
        self.assertEqual(self.submit(token)[0], 200)
        before = self.status()
        self.assertFalse(any("handle" in item or "pr" in item for item in before["activities"]))
        self.assertNotIn(token.encode(), self.db.read_bytes())
        self.assertNotIn(b"2001:db8", self.db.read_bytes())
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.record(102, GAPS[1]["id"], "ACCEPTED")
        self.assertEqual(self.status()["active"], 1)
        with patch("deploy.desk.time.time", return_value=START + 1):
            self.record(102, GAPS[0]["id"], "ACCEPTED", 2)
        outcome = self.status(START + 1)
        self.assertEqual(outcome["active"], 0)
        self.assertEqual(outcome["activities"][0]["kind"], "accepted")
        self.assertEqual(outcome["leaderboard"], [{"handle": "alice", "accepted": 1}])

    def test_network_limit_groups_ipv6_neighbors_without_leaking_addresses(self):
        for i in range(1, 4):
            self.assertEqual(self.request("claim", {"handle": f"Agent{i}"}, ip=f"2001:db8::{i}")[0], 201)
        self.assertEqual(self.request("claim", {"handle": "Agent4"}, ip="2001:db8::4")[0], 429)
        self.assertEqual(self.request("claim", {"handle": "Agent4"}, ip="2001:db8:0:1::4")[0], 201)

    def test_automatic_claims_spread_across_programs(self):
        programs = ["foundation", "foundation", "coverage", "coverage", "exceptions"]
        self.desk = Desk(self.db, [g | {"program": p} for g, p in zip(GAPS, programs)], SECRET)
        allocated = []
        for handle in ("ada", "bob", "carol"):
            status, assignment = self.request("claim", {"handle": handle})
            self.assertEqual(status, 201)
            allocated.append(assignment["gap"]["program"])
        self.assertEqual(allocated, ["foundation", "coverage", "exceptions"])

    def test_parallel_leases_preserve_checking_and_release_unstarted_after_acceptance(self):
        self.desk = Desk(self.db, [GAPS[0] | {"parallel": True}], SECRET)
        tokens = [self.claim(handle) for handle in ("Alice", "Bob", "Carol")]
        for i, token in enumerate(tokens):
            self.assertEqual(self.submit(token, pr=8+i)[0], 200)
        for i, handle in enumerate(("Alice", "Bob")):
            body = self.authorization(pr=8+i, handle=handle, run_id=102+i)
            self.assertEqual(self.request("authorize", body, sign=True)[0], 200)
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "checking"})
        with patch("deploy.desk.time.time", return_value=START+1):
            self.record(102, GAPS[0]["id"], "ACCEPTED")
        self.assertEqual(self.request("beat", {}, token=tokens[2])[0], 410)
        self.assertEqual(self.status(START+1)["active"], 1)
        self.assertEqual(self.request("pending", {}, sign=True)[1]["pending"], [])
        self.assertEqual(self.request("claim", {"handle": "Dave", "gap": GAPS[0]["id"]})[0], 409)

    def test_statement_changed_after_claim_cannot_authorize(self):
        self.assertEqual(self.submit(self.claim())[0], 200)
        updated = [GAPS[0] | {"statement": "different statement"}, *GAPS[1:]]
        self.desk = Desk(self.db, updated, SECRET)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 409)


if __name__ == "__main__":
    unittest.main()
