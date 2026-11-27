"""Recheck the two tail budgets using S1 Theorem C's series directly."""

import sys
from decimal import Context, ROUND_CEILING, localcontext
from fractions import Fraction
from math import ceil
from pathlib import Path
from unittest.mock import patch


def check(upstream):
    certificate = upstream / "certificate"
    sys.path.insert(0, str(certificate))
    sys.path.insert(0, str(certificate / "linear_sieve"))
    # cn_certify sets 40-digit ceiling rounding when imported. Keep that
    # context local and retain the exact stored upper bounds as rationals.
    with localcontext(Context(prec=40, rounding=ROUND_CEILING)):
        import cn_certify

        cutoff = 160
        rows = cn_certify.certify(cutoff)
    from all_even_1p4.elementary import exp_iv
    from all_even_1p4.interval import Iv
    from all_even_1p4.sieve_functions import h_upper
    from all_even_1p4_ext import tail_x31

    decay = Fraction(9607, 10000)
    # S1 step 8 gives M_n <= decay**(n-1). The full remaining
    # geometric sum is an upper bound for either parity separately.
    remainder = decay**cutoff / (1 - decay)
    totals = []
    for parity in (0, 1):
        total = sum(Fraction(row["M"]) for n, row in rows.items() if n % 2 == parity)
        totals.append(Fraction(ceil(1000 * (total + remainder)), 1000))
    print(f"even M sum <= {totals[0]}, odd M sum (n >= 3) <= {totals[1]}")
    scale = Iv(2) * exp_iv(Iv(2))

    class SeriesBounds:
        def f_lower(self, s):
            if s.lo < 2:
                raise ValueError("even-series argument below 2")
            return Iv(1) - scale * h_upper(s) * Iv.from_fraction(totals[0])

        def F_upper(self, s):
            if s.lo < 3:
                raise ValueError("the n=1 term can only be omitted for s >= 3")
            return Iv(1) + scale * h_upper(s) * Iv.from_fraction(totals[1])

    # Keep the upstream levels, remainders, constants and interval arithmetic;
    # only the bounds on the two limiting sieve functions are replaced.
    with patch.object(tail_x31, "grid", return_value=SeriesBounds()):
        for recursion, m in (("old", 24), ("new", 22)):
            params = tail_x31.X31Tail.from_files(500, m, "3.01", 80, recursion, slices=2000)
            result = tail_x31.certify(params)
            print(f"{recursion}: main >= {result['main']}, errors <= {result['err']}, "
                  f"net >= {result['net']}")
            if not result["ok"]:
                raise ValueError(f"{recursion} lower bound did not prove positivity")


if __name__ == "__main__":
    check(Path(sys.argv[1]).resolve())
