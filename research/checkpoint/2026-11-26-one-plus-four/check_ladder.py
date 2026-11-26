"""Check the published ladder using only integers and exact rational numbers."""

import json
import sys
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def first_odd_primes(count):
    primes = []
    candidate = 3
    while len(primes) < count:
        if all(candidate % p for p in primes if p <= isqrt(candidate)):
            primes.append(candidate)
        candidate += 2
    return primes


def check(path):
    rows = json.loads(path.read_text(encoding="utf-8"))
    require(len(rows) == 58, "expected 58 slabs")
    previous = 4 * 10**18
    for i, r in enumerate(rows, 1):
        lo, hi = int(r["x_lo"]), int(r["x_hi"])
        z, y = int(r["z"]), int(r["y"])
        require(previous == lo < hi, f"slab {i}: continuity")
        require(2 < z < y and min(z * y**4, y**5) >= hi, f"slab {i}: weight")
        primes = first_odd_primes(r["a"])
        for side, parity, multiplier in (("low", 1, 1), ("up", 0, y)):
            caps, ends = r[side + "_caps"], r[side + "_ends"]
            require(len(ends) == len(caps) + 1 and ends[0] == z and
                    ends[-1] == primes[-1] + 1 and all(a > b for a, b in zip(ends, ends[1:])),
                    f"slab {i}: {side} endpoints")
            degrees = [v - u for u, v in zip([0] + caps, caps)]
            require(all(d >= 0 for d in degrees) and all(c % 2 == parity for c in caps),
                    f"slab {i}: {side} caps")
            level = multiplier * prod(primes) * prod(b**d for b, d in zip(ends, degrees))
            require(level**2 <= lo, f"slab {i}: {side} distribution level")
        errors = sum(Fraction(r[k]) for k in ("err_a_hi", "err_aq_hi", "err_q2_hi"))
        require(Fraction(r["err_hi"]) >= errors >= 0, f"slab {i}: sum of errors")
        require(0 < Fraction(r["net_lo"]) <= Fraction(r["main_lo"]) - Fraction(r["err_hi"]),
                f"slab {i}: conservative positive net")
        previous = hi
    require(previous == 10**500, "wrong final endpoint")
    worst = min(rows, key=lambda r: Fraction(r["net_lo"]))
    print(f"58 slabs passed; minimum reported lower bound = {worst['net_lo']}")
    print(f"Minimum on [10^{len(worst['x_lo'])-1}, 10^{len(worst['x_hi'])-1})")


if __name__ == "__main__":
    check(Path(sys.argv[1]))
