"""Exact integer budget certificate, Breaker first; deterministic, no seed.

Not a minimax solver. A failed certificate is inconclusive.
Run: python upper-bound/experiments/lookahead.py
"""
from math import sqrt
from itertools import product


def outside_cost(a, b, n):
    # Free degrees p,q are safe precisely when neither attachment creates
    # more than n immediate winning edges on the other side.
    return min(a, b, max(a-n, 0) + max(b-n, 0))


def certify(n, m):
    a = b = 1
    while a + b <= m:
        budget = (a + b - 1) * n  # after Breaker's move
        outside = m - a - b
        threat_cost = a*b + outside*outside_cost(a, b, n)
        if threat_cost > budget:
            return a, b
        # Separate lower bound: every edge leaving the smaller component
        # must be deleted to stop its growth. Do not add overlapping costs.
        if a*(m-a) <= budget:
            return None
        a += 1
        if a > b:
            a, b = b, a
    return None


def verify_cost_formula():
    for n in range(1, 5):
        for a, b in product(range(1, 9), repeat=2):
            exact = min(a+b-p-q for p in range(a+1) for q in range(b+1)
                        if not (p > 0 and q > n)
                        and not (q > 0 and p > n))
            assert exact == outside_cost(a, b, n)


if __name__ == '__main__':
    verify_cost_formula()
    print('Exhaustive local degree check passed; Breaker-first budget certificate.')
    print('n,m,m/n,smaller_at_certificate,larger_at_certificate')
    for n in [1, 2, 5, 10, 25, 50, 100, 250, 1000, 10000]:
        lo, hi = 2*n-1, 4*n
        while hi-lo > 1:
            mid = (lo+hi)//2
            if certify(n, mid) is None:
                lo = mid
            else:
                hi = mid
        m = hi
        witness = certify(n, m)
        print(f'{n},{m},{m/n:.8f},{witness[0]},{witness[1]}')
    print(f'Analytic coefficient: 2+sqrt(3) = {2+sqrt(3):.10f}')
