"""Replay two Goldbach representations at every even target in [10^316, 10^316+2^21).

Requires Python 3.10+ and PARI/GP with primecert. The ECPP chains are generated
and validated locally. The digest uses two little-endian 32-bit anchor offsets per
target, keeping the first two in the order below. The original 43 anchors come from
the accepted Rfc11Top316AnchorBank theorem. The final 57 are new for this interval.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from math import gcd, isqrt
import struct
import subprocess

ORIGINAL_OFFSETS = [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447]
EXTRA_OFFSETS = [330557, 313757, 609941, 206409, 91967, 237449, 239139, 180803, 99741, 110081, 94527, 121439, 483129, 400877, 295203, 193973, 152721, 363449, 390417, 184121, 483093, 91493, 91821, 509519, 219633, 352721, 455769, 302991, 545687, 239171, 577803, 114683, 87351, 82283, 542927, 158139, 585761, 271551, 261707, 189897, 247709, 180297, 131993, 226509, 155417, 615513, 387309, 546191, 175097, 320637, 169751, 100161, 222323, 118961, 122703, 80787, 119289]
EVEN_TARGETS = 1 << 20
EXPECTED_DIGEST = "8c43d5879c6c01a99fc241b904ea79b7b421f0f86acd8691be97bf4da6aaa073"

def certify(gp, offset):
    script = ("default(parisizemax,536870912)\n"
              f"p=10^316-{offset};c=primecert(p);\n"
              'if(primecertisvalid(c),print("VALID"),print("FAILED"));\nquit\n')
    proc = subprocess.run([gp, "-fq"], input=script, capture_output=True, text=True, check=True)
    if proc.stdout.strip() != "VALID":
        raise RuntimeError(f"PARI certificate verification failed at offset {offset}")

def prime_table(bound):
    table = bytearray([1]) * (bound + 1)
    table[:2] = bytes(2)
    for p in range(2, isqrt(bound) + 1):
        if table[p]:
            table[p*p::p] = bytes((bound - p*p) // p + 1)
    return table

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    offsets = ORIGINAL_OFFSETS + EXTRA_OFFSETS
    assert len(offsets) == len(set(offsets)) == 100
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(lambda t: certify(args.gp, t), offsets))
    print("100 large prime certificates verified.", flush=True)
    bound = max(offsets) + 2*(EVEN_TARGETS-1)
    prime = prime_table(bound)
    histogram = [0] * (len(offsets) + 1)
    old_misses = [0, 0]
    obstruction_classes = {0: {}, 1: {}}
    digest = hashlib.sha256()
    for k in range(EVEN_TARGETS):
        shift = 2*k
        hits = [t for t in offsets if prime[t+shift]]
        old_hits = sum(prime[t+shift] for t in ORIGINAL_OFFSETS)
        old_misses[0] += old_hits == 0
        old_misses[1] += old_hits < 2
        if old_hits == 0 and shift > 105 and gcd(10**316 + shift, 105) == 1:
            obstruction_classes[shift % 3].setdefault(shift % 105, shift)
        if len(hits) < 2:
            raise ValueError(f"insufficient witnesses at 10^316 + {shift}")
        histogram[len(hits)] += 1
        digest.update(struct.pack("<II", *hits[:2]))
    total = sum(i*n for i, n in enumerate(histogram))
    assert sum(histogram) == EVEN_TARGETS and total == 15224990
    assert histogram[2] == 366 and old_misses == [4498, 29798]
    assert digest.hexdigest() == EXPECTED_DIGEST
    for group, rows in obstruction_classes.items():
        assert len(rows) == 24
        allowed = [t for t in range(105) if gcd(10**316 - t, 105) == 1]
        for t in allowed:
            count = sum(gcd(d+t, 105) == 1 for d in rows.values())
            assert count <= (15 if t % 3 == (2 if group == 0 else 0) else 0)
    print(f"{EVEN_TARGETS} even targets, {total} distinct representations in the bank, minimum 2.")
    print(f"{histogram[2]} targets attain the minimum. Smaller summands are at most {bound}.")
    print(f"Witness SHA-256 {digest.hexdigest()}")
    print("Each residue group needs 48 incidences at 15 per new anchor. Two disjoint groups require at least eight new anchors.")

if __name__ == "__main__":
    main()
