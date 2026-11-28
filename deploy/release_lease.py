#!/usr/bin/env python3
"""Inspect or release orphaned, unsubmitted research leases on the Goldbach host.

A claim response can be lost (for example, a client timeout).  The desk then keeps
the year-9999 lease, but only the SHA-256 of its token is stored, so the client can
no longer call ``/api/desk/release``.  This host-side admin tool lets a maintainer
find such rows and mark them released without touching a lease that has already
registered a PR/run or received a verdict.

Run from ``/opt/goldbach-web`` so ``desk`` is importable.  The default is a dry run;
pass ``--yes`` to write.  Back up the database first, for example:

    sudo sqlite3 /var/lib/goldbach-web/verdicts.sqlite3 \\
      ".backup '/root/verdicts-$(date +%s).sqlite3'"
"""

import argparse
import sqlite3
import time
from contextlib import closing
from pathlib import Path

from desk import RELEASE_REASONS


DEFAULT_DB = Path("/var/lib/goldbach-web/verdicts.sqlite3")


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("handle", help="GitHub login whose lease should be inspected")
    parser.add_argument("--db", type=Path, default=DEFAULT_DB, help="verdicts.sqlite3 path")
    parser.add_argument("--gap", help="only this frozen task id")
    parser.add_argument(
        "--older-than-minutes",
        type=int,
        default=0,
        help="only leases claimed at least this many minutes ago (default: 0)",
    )
    parser.add_argument(
        "--reason",
        default="abandoned",
        choices=sorted(RELEASE_REASONS),
        help="release reason written to the audit column",
    )
    parser.add_argument("--yes", action="store_true", help="write the release (default: dry run)")
    return parser.parse_args()


def main():
    args = parse_args()
    handle = args.handle.strip().lower()
    if not handle:
        raise SystemExit("handle must not be empty")

    now = int(time.time())
    with closing(sqlite3.connect(f"file:{args.db}?mode=rw", uri=True, timeout=15)) as conn:
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA busy_timeout=15000")

        query = """
            SELECT rowid, token_hash, gap, kind, claimed_at, expires_at,
                   submitted_at, run_id
            FROM goldbach_leases
            WHERE lower(handle) = ?
              AND released_at IS NULL
              AND finished_at IS NULL
              AND expires_at > ?
        """
        params = [handle, now]
        if args.gap:
            query += " AND gap = ?"
            params.append(args.gap)
        if args.older_than_minutes > 0:
            query += " AND claimed_at <= ?"
            params.append(now - args.older_than_minutes * 60)
        query += " ORDER BY claimed_at, rowid"

        rows = conn.execute(query, params).fetchall()
        if not rows:
            print(f"No active leases found for handle {handle!r}.")
            return

        eligible = []
        print(f"Active leases for {handle!r}:")
        for row in rows:
            state = "orphaned" if row["submitted_at"] is None and row["run_id"] is None else "in use"
            age = max(0, now - int(row["claimed_at"])) // 60
            print(
                f"  rowid={row['rowid']} gap={row['gap']} kind={row['kind']} "
                f"claimed={age}m ago state={state} run_id={row['run_id']}"
            )
            if state == "orphaned":
                eligible.append(row)

        if not eligible:
            print("No orphaned unsubmitted leases to release.")
            return

        if not args.yes:
            print(
                f"Dry run: {len(eligible)} orphaned lease(s) would be marked "
                f"released_at=now, release_reason={args.reason!r}. Pass --yes to write."
            )
            return

        with conn:
            conn.execute("BEGIN IMMEDIATE")
            cursor = conn.executemany(
                """
                UPDATE goldbach_leases
                SET released_at = ?, release_reason = ?
                WHERE token_hash = ?
                  AND submitted_at IS NULL
                  AND run_id IS NULL
                  AND released_at IS NULL
                  AND finished_at IS NULL
                """,
                [(now, args.reason, row["token_hash"]) for row in eligible],
            )
            released = cursor.rowcount
        print(f"Released {released} orphaned lease(s) for {handle!r}.")


if __name__ == "__main__":
    main()
