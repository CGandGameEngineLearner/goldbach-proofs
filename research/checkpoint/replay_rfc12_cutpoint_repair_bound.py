"""Bound the number of extra anchors needed for two-cover on the RFC1.2 cutoff.

Run alongside replay_rfc12_cutpoint_million.py using Python 3.10 or later.
No PARI installation is needed. Both sieves only discard provably composite
integers. The bound applies to all offsets 0 <= t <= 2,712,663.
"""
from replay_rfc12_cutpoint_million import EVEN_TARGETS, ORIGINAL_OFFSETS, prime_table


def main():
    cutoff = 10**316
    maximum_offset = 2_712_663
    prime = prime_table(2*EVEN_TARGETS + maximum_offset)
    # If cutoff-t is prime then no prime up to 32,000 divides it.
    possible = bytearray([1]) * (maximum_offset + 1)
    for p in range(2, 32_001):
        if prime[p]:
            residue = cutoff % p
            possible[residue::p] = bytes(1 + (maximum_offset-residue)//p)

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
