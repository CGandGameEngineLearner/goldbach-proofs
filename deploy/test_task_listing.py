import gzip
import json
import unittest
from unittest.mock import MagicMock, patch

from tools import goldbach


class TaskListingTests(unittest.TestCase):
    def test_live_board_excludes_unclaimable_tasks_and_keeps_parallel_claims(self):
        board = {
            "desk": {"assignments": {"parallel-task": "working", "occupied": "working"}},
            "gaps": [
                {"id": "parallel-task", "parallel": True, "points": 4},
                {"id": "occupied"},
                {"id": "closed", "claims_closed": True},
                {"id": "refuted", "refutation": {"status": "verified"}},
                {"id": "proved", "proved": True},
                {"id": "resolved", "resolved": True},
                {"id": "challenge", "challenge_only": True, "points": 7},
            ],
        }
        opener = MagicMock()
        response = opener.open.return_value.__enter__.return_value
        response.headers = {"Content-Encoding": "gzip"}
        response.read.return_value = gzip.compress(json.dumps(board).encode())
        with patch.object(goldbach.urllib.request, "build_opener", return_value=opener):
            listing = goldbach.list_tasks("twin-primes", 1)
        self.assertEqual(listing, {
            "problem": "twin-primes", "available": 2,
            "tasks": [{"id": "challenge", "points": 7, "challenge_only": True}],
        })
        request = opener.open.call_args.args[0]
        self.assertEqual(request.get_method(), "GET")
        self.assertTrue(request.full_url.endswith("/problems/twin-primes/api/status?view=board-gzip"))
