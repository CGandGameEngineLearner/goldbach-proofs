"""Replay the RFC1 prime pairs, lifted wheel and endpoint inequalities with Python 3."""

from fractions import Fraction
from functools import cache
from math import factorial, gcd, isqrt

C = 4 * 10**18
WITNESSES = (
    211, 313, 509, 317, 127, 251, 127, 1213, 131, 137, 139, 137, 139, 337, 239, 149,
    151, 149, 151, 3, 5, 7, 163, 11, 13, 3, 5, 7, 367, 11, 13, 181,
    17, 19, 379, 3, 5, 7, 29, 11, 13, 47, 17, 19, 41, 23, 211, 47,
    29, 31, 53, 67, 37, 59, 41, 43, 227, 47, 769, 71, 53, 3, 5, 7,
)

WHEEL = (
    (17, 30047, 60077),
    (19, 150169, 210229),
    (23, 60083, 210233),
    (181, 30211, 90271),
    (29, 30059, 60089),
    (37, 90127, 120157),
    (41, 30071, 60101),
    (43, 60103, 120163),
    (31, 60091, 90121),
    (47, 60107, 120167),
    (53, 150203, 180233),
    (67, 30097, 60127),
)

# Each entry gives a Lucas witness and all distinct prime divisors of n−1.
LUCAS = {
    1077697: (5, (2, 3, 1871)),
    1786469: (2, (2, 31, 14407)),
    3572939: (2, (2, 1786469)),
    4318891: (2, (2, 3, 5, 19, 7577)),
    4623217: (23, (2, 3, 13, 31, 239)),
    5220511: (6, (2, 3, 5, 174017)),
    5548607: (5, (2, 7, 251, 1579)),
    6363769: (7, (2, 3, 265157)),
    8541289: (43, (2, 3, 7, 269)),
    15924371: (2, (2, 5, 7, 11, 20681)),
    42393521: (3, (2, 5, 13, 40763)),
    149855393: (3, (2, 1307, 3583)),
    244138709: (2, (2, 11, 5548607)),
    299710787: (2, (2, 149855393)),
    594085421: (3, (2, 5, 43, 331, 2087)),
    777448979: (2, (2, 73, 1301, 4093)),
    2712263549: (2, (2, 157, 4318891)),
    2929664509: (6, (2, 3, 244138709)),
    13994081623: (3, (2, 3, 777448979)),
    103100510729: (3, (2, 43, 299710787)),
    37379684141669: (2, (2, 11, 389, 18913, 115471)),
    566251415628539: (2, (2, 241, 401, 2929664509)),
    100000000000000003: (2, (2, 3, 7, 61, 65701, 594085421)),
    181818181818181813: (5, (2, 3, 29, 192631, 2712263549)),
    399999999999999979: (2, (2, 3, 23, 211, 239851, 6363769)),
    1000000000000000009: (7, (2, 3, 97, 26209, 32779, 166667)),
    3999999999999998803: (2, (2, 3, 229, 8147, 8429, 42393521)),
    3999999999999999349: (6, (2, 3, 31, 61, 283, 491, 5220511)),
    3999999999999999497: (3, (2, 883, 566251415628539)),
    3999999999999999691: (3, (2, 3, 5, 29, 41, 37379684141669)),
    3999999999999999761: (7, (2, 5, 3572939, 13994081623)),
    3999999999999999791: (11, (2, 5, 399999999999999979)),
    3999999999999999883: (2, (2, 3, 19, 157, 547, 25657, 15924371)),
    3999999999999999887: (5, (2, 11, 181818181818181813)),
    4000000000000000037: (2, (2, 1000000000000000009)),
    4000000000000000049: (3, (2, 13, 487, 4623217, 8541289)),
    4000000000000000069: (6, (2, 3, 1077697, 103100510729)),
    4000000000000000121: (3, (2, 5, 100000000000000003)),
}


@cache
def prime(n):
    if n < 10**6:
        return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))
    witness, factors = LUCAS[n]
    remaining = n - 1
    for q in factors:
        if not 2 <= q < n or remaining % q or not prime(q):
            return False
        while remaining % q == 0:
            remaining //= q
        if gcd(pow(witness, (n - 1) // q, n) - 1, n) != 1:
            return False
    return remaining == 1 and pow(witness, n - 1, n) == 1


def exp_bounds(x):
    # Sum through degree 24. The remaining ratios are at most x/26.
    x = Fraction(x)
    partial = sum(x**k / factorial(k) for k in range(25))
    return partial, partial + x**25 / factorial(25) / (1 - x/26)


def verify():
    assert len(WITNESSES) == 64
    for j, p in enumerate(WITNESSES, 1):
        assert prime(p) and prime(C + 2*j - p)
    remaining = set(range(0, 30030, 2))
    for row in WHEEL:
        base = row[0]
        assert gcd(base, 30030) == 1
        assert all(prime(p) and p <= 210233 and p % 30030 == base for p in row)
        assert all(len({p % m for p in row}) == 3 for m in (17, 19))
        remaining = {a for a in remaining if gcd(a - base, 30030) != 1}
    assert not remaining
    assert 30030 * 17 * 19 == 9699690 and 210235 < 3**15
    assert exp_bounds(Fraction(19, 5))[1] < 45 and exp_bounds(3)[1] < 23
    assert exp_bounds(5)[1] < Fraction(297, 2) < 48 * Fraction(31, 10)
    assert exp_bounds(Fraction(31, 10))[1] < 23
    assert exp_bounds(4)[0] > 50 and 50**11 > C and 44**2 * 10**6 < isqrt(C)


if __name__ == "__main__":
    verify()
    print("Verified 64 prime pairs, 12 wheel triples, 15015 even residues and the endpoint bounds.")
