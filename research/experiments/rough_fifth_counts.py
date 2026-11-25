"""Reproduce the preselected rough-complement stress test with integer cutoffs."""
from array import array
from bisect import bisect_right
from fractions import Fraction
from math import isqrt


LARGE_SAMPLE = (100000, 100002, 131072, 262140, 510510, 1000000, 1048576, 1999998, 2000000)
limit = max(LARGE_SAMPLE)
smallest = array('I', range(limit + 1))
for prime in range(2, isqrt(limit) + 1):
    if smallest[prime] == prime:
        for n in range(prime**2, limit + 1, prime):
            if smallest[n] == n:
                smallest[n] = prime
primes = [n for n in range(2, limit + 1) if smallest[n] == n]
omega = bytearray(limit + 1)
squareful = bytearray(limit + 1)
for n in range(2, limit + 1):
    factor = smallest[n]
    quotient = n // factor
    omega[n] = 1 + omega[quotient]
    squareful[n] = squareful[quotient] or quotient % factor == 0


def counts(n):
    z = 1
    while (z + 1)**5 <= n:
        z += 1
    start = bisect_right(primes, n // 3)
    end = bisect_right(primes, (2*n - 1) // 3)
    hist = [0]*5
    d = 0
    for p in primes[start:end]:
        r = n - p
        if r > 1 and smallest[r] > z:
            hist[omega[r]] += 1
            d += squareful[r]
    m = sum(hist)
    l = hist[2] + hist[4] - hist[1] - hist[3]
    assert 2*hist[1] == m - l - 2*hist[3]
    assert z*d <= n
    return m, hist[3], l, d


rows = [(n, *counts(n)) for n in range(100, 20001, 2)]
for low, high in [(100, 20000), (1000, 20000), (10000, 20000)]:
    block = [row for row in rows if low <= row[0] <= high]
    positive = [row for row in block if row[1]]
    t, nt = max((Fraction(t, m), n) for n, m, t, l, d in positive)
    lam, nl = max((Fraction(l, m), n) for n, m, t, l, d in positive)
    print('Range', low, high, 'size', len(block), 'M=0', len(block)-len(positive),
          'T3/M max', t, 'last attained', nt, 'L/M max', lam, 'last attained', nl,
          '10T3>3M', sum(10*t > 3*m for n, m, t, l, d in block),
          '5L>=2M', sum(5*l >= 2*m for n, m, t, l, d in block),
          '10L>3M', sum(10*l > 3*m for n, m, t, l, d in block))
print('N, M, T3, L, D, T3/M, L/M')
for n in LARGE_SAMPLE:
    m, t, l, d = counts(n)
    print(n, m, t, l, d, f'{t/m:.6f}', f'{l/m:.6f}')
