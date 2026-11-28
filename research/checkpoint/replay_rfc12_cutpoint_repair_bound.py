"""Bound the number of extra anchors needed for two-cover on the RFC1.2 cutoff.

Run alongside replay_rfc12_cutpoint_million.py using Python 3.10 or later.
No PARI installation is needed. Both sieves only discard provably composite
integers. The bound applies to all offsets 0 <= t <= 2,712,663.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path
from replay_rfc12_cutpoint_million import EVEN_TARGETS, ORIGINAL_OFFSETS, prime_table


def fermat_survivors(offsets):
    try:
        from gmpy2 import powmod
    except ImportError:
        powmod = pow
    cutoff = 10**316
    return [t for t in offsets if powmod(2, cutoff-t-1, cutoff-t) == 1]


def weighted_bound(possible, prime, jobs):
    # Every prime cutoff-t passes base-2 Fermat. Any composite passing the
    # test remains in this upper bound on the possible contributors.
    offsets = [t for t, allowed in enumerate(possible) if allowed]
    blocks = (offsets[i:i+512] for i in range(0, len(offsets), 512))
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        survivors = [t for block in pool.map(fermat_survivors, blocks) for t in block]
    evidence = json.loads(Path(__file__).with_name("rfc12_cutpoint_repair_weights.json").read_bytes())
    total = 0
    for group in (0, 1):
        record = evidence[str(group)]
        rows = record["weighted_holes"]
        assert len({h for h,w in rows}) == len(rows)
        for h,w in rows:
            assert isinstance(h,int) and isinstance(w,int) and w>0
            assert 1000 <= h < 2*EVEN_TARGETS and h%2 == 0 and h%3 == group
            assert all(not prime[t+h] for t in ORIGINAL_OFFSETS)
        mass = sum(w for h,w in rows)
        largest = max(sum(w for h,w in rows if prime[h+t]) for t in survivors if (t+group)%3)
        needed = (2*mass+largest-1)//largest
        assert (mass,largest,needed) == (record["weight_sum"],record["maximum_incidence"],record["lower_bound"])
        print(f"Group {group}: total weight {mass}, largest incidence {largest}, at least {needed} offsets.", flush=True)
        total += needed
    print(f"{len(survivors)} Fermat survivors; at least {total} additional anchors by weighted incidence.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--weighted", action="store_true", help="check the stronger integer-weight certificate; optional gmpy2 speeds up Fermat tests")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    cutoff = 10**316
    maximum_offset = 2_712_663
    prime = prime_table(2*EVEN_TARGETS + maximum_offset)
    # If cutoff-t is prime then no prime up to 32,000 divides it.
    possible = bytearray([1]) * (maximum_offset + 1)
    for p in range(2, 32_001):
        if prime[p]:
            residue = cutoff % p
            possible[residue::p] = bytes(1 + (maximum_offset-residue)//p)

    if args.weighted:
        weighted_bound(possible, prime, args.jobs)
        return
    total_needed = 0
    for group, offset_class in [(0, 2), (1, 0)]:
        holes = [h for h in range(1000, 2*EVEN_TARGETS, 2)
                 if h%3 == group and all(not prime[h+t] for t in ORIGINAL_OFFSETS)]
        # cutoff = 1 mod 3 excludes t = 1 mod 3. In this group, whichever
        # other residue makes h+t a multiple of 3 cannot represent a hole.
        capacities = (sum(prime[t+h] for h in holes)
                      for t in range(offset_class, maximum_offset+1, 3) if possible[t])
        maximum = max(capacities)
        needed = (2*len(holes) + maximum - 1)//maximum
        print(f"Group {group}: {len(holes)} holes, maximum {maximum} incidences, at least {needed} offsets.", flush=True)
        assert (len(holes), maximum, needed) == [(3286, 955, 7), (1199, 375, 7)][group]
        total_needed += needed
    print(f"The two disjoint residue classes require at least {total_needed} additional anchors.")


if __name__ == "__main__":
    main()
