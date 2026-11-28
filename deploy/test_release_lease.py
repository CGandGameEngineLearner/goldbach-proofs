"""Tests for the orphaned-lease admin tool."""

import sqlite3
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_lease


GAP = "L-test-orphaned-lease"


class ReleaseLeaseTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.db = Path(self.tmp.name) / "verdicts.sqlite3"
        conn = sqlite3.connect(self.db)
        conn.executescript(
            """
            CREATE TABLE goldbach_leases (
                token_hash TEXT PRIMARY KEY,
                gap TEXT NOT NULL,
                handle TEXT NOT NULL,
                claimed_at INTEGER NOT NULL,
                expires_at INTEGER NOT NULL,
                kind TEXT NOT NULL,
                submitted_at INTEGER,
                run_id INTEGER,
                released_at INTEGER,
                release_reason TEXT,
                finished_at INTEGER
            );
            """
        )
        now = int(time.time())
        conn.execute(
            "INSERT INTO goldbach_leases VALUES (?,?,?,?,?,?,?,?,?,?,?)",
            ("a" * 64, GAP, "yuhengjie", now - 1800, 253402300799, "prove", None, None, None, None, None),
        )
        conn.execute(
            "INSERT INTO goldbach_leases VALUES (?,?,?,?,?,?,?,?,?,?,?)",
            ("b" * 64, GAP, "yuhengjie", now - 600, 253402300799, "prove", now - 500, 123456, None, None, None),
        )
        conn.commit()
        conn.close()

    def tearDown(self):
        self.tmp.cleanup()

    def run_tool(self, *extra):
        argv = ["release_lease.py", "YuHengjie", "--db", str(self.db), "--gap", GAP, *extra]
        with patch.object(sys, "argv", argv):
            release_lease.main()

    def rows(self):
        conn = sqlite3.connect(self.db)
        conn.row_factory = sqlite3.Row
        result = {row["token_hash"]: row for row in conn.execute("SELECT * FROM goldbach_leases")}
        conn.close()
        return result

    def test_dry_run_is_default_and_does_not_write(self):
        self.run_tool()
        rows = self.rows()
        self.assertIsNone(rows["a" * 64]["released_at"])
        self.assertIsNone(rows["b" * 64]["released_at"])

    def test_yes_releases_only_the_orphan(self):
        self.run_tool("--yes")
        rows = self.rows()
        self.assertIsNotNone(rows["a" * 64]["released_at"])
        self.assertEqual(rows["a" * 64]["release_reason"], "abandoned")
        self.assertIsNone(rows["b" * 64]["released_at"])
        self.assertIsNone(rows["b" * 64]["release_reason"])

    def test_older_than_filter_can_exclude_the_recent_orphan(self):
        self.run_tool("--older-than-minutes", "60", "--yes")
        rows = self.rows()
        self.assertIsNone(rows["a" * 64]["released_at"])
        self.assertIsNone(rows["b" * 64]["released_at"])


if __name__ == "__main__":
    unittest.main()
