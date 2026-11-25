import hashlib
import unittest
from graphlib import CycleError

from frontier import prepare, review_plan


class FrontierTests(unittest.TestCase):
    def setUp(self):
        self.parent = "L-goldbach-parent"
        self.child = "L-goldbach-aux"
        self.bridge = "L-goldbach-bridge"
        self.gaps = [{"id": self.parent, "statement": "P", "plain_statement": {"zh": "P"}}]
        self.snapshot = {"gaps": [{**self.gaps[0], "proved": False}],
                         "desk": {"assignments": {self.parent: "working"}}}
        self.plan = {
            "version": 1, "problem": "goldbach", "base_revision": "a" * 40,
            "parent": {"id": self.parent, "statement_sha256": hashlib.sha256(b"P").hexdigest()},
            "tasks": [{"id": self.child, "statement": "A", "depends_on": []},
                      {"id": self.bridge, "statement": "(A) → (P)", "depends_on": []}],
            "links": [{"kind": "sufficient_reduction", "inputs": [self.child],
                       "output": self.parent, "bridge": self.bridge}],
        }

    def review(self):
        return review_plan(self.plan, self.gaps, self.snapshot, "goldbach", "a" * 40)

    def test_bridge_preserves_active_parent_and_exact_types(self):
        result = self.review()
        self.assertEqual(result["parent"]["assignment"], "working")
        self.assertEqual(result["bridge_obligations"], [{
            "bridge": self.bridge, "expected_type": "(A) → (P)", "matches_literal_type": True}])

    def test_parent_as_transitive_prerequisite(self):
        self.plan["tasks"][0]["depends_on"] = [self.parent]
        with self.assertRaises(CycleError):
            self.review()

    def test_disconnected_new_task(self):
        self.plan["tasks"].append({"id": "L-goldbach-extra", "statement": "B", "depends_on": []})
        with self.assertRaisesRegex(ValueError, "without a path"):
            self.review()

    def test_stale_live_statement(self):
        self.snapshot["gaps"][0]["statement"] += " "
        with self.assertRaisesRegex(ValueError, "catalogue differ"):
            self.review()

    def test_already_accepted_parent(self):
        self.snapshot["gaps"][0]["proved"] = True
        self.assertEqual(prepare(self.gaps, self.snapshot)["open"], 0)
        with self.assertRaisesRegex(ValueError, "open proposition"):
            self.review()
