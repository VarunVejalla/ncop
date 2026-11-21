"""Three-Maker-move auxiliary-component search, Breaker first.

Deterministic, exhaustive on the stated degree grids; no random seed.
The scaled search is an extremal relaxation, not a full game solver.
Run: python upper-bound/experiments/three_move_search.py
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import sqrt
import json


def blocking_cost(p, q, n):
    """Exact deletions needed to remove both possible two-move attachments."""
    return min(p, q, max(p-n, 0)+max(q-n, 0))


def dangerous_pair(u, v, n):
    return blocking_cost(u[0]+v[0], u[1]+v[1], n) > n


def degree_types(k, n):
    return [(p,q) for p in range(k+1) for q in range(k+1)
            if blocking_cost(p,q,n) == 0]


def exact_fixed_state(n, k, outside):
    """Global minimum over integer degrees for this restricted threat family.

    Every safe outside graph must delete each dangerous pair. Enumerating
    multisets would be expensive. Quadratic mass shifting leaves <=1 low
    (safe self-pair) and <=1 high (dangerous self-pair) degree type.
    For integer counts a concave/linear shift also ends at integer endpoints.
    High types are mutually dangerous: each coordinate >n/2, sum >3n/2.
    Thus all minimizers can be represented with these two types.
    """
    types=degree_types(k,n)
    low=[t for t in types if not dangerous_pair(t,t,n)]
    high=[t for t in types if dangerous_pair(t,t,n)]
    best=None
    witness=None
    for lo in low:
        for hi in high + [lo]:
            cross=dangerous_pair(lo,hi,n)
            dh=dangerous_pair(hi,hi,n)
            for h in range(outside+1):
                l=outside-h
                cost=l*(2*k-sum(lo))+h*(2*k-sum(hi))
                cost+=cross*l*h+dh*h*(h-1)//2
                if best is None or cost<best:
                    best,witness=cost,{'low':lo,'high':hi,'high_count':h}
    return k*k+best,witness


@dataclass(frozen=True)
class StateMinimum:
    margin: float
    low: tuple
    high: tuple
    high_fraction: float


def scaled_types(x, subdivisions):
    g=[F(i,subdivisions) for i in range(subdivisions+1)]
    # Degree into either component can exceed the bias only when the
    # opposite degree is zero; otherwise two-move safety caps both at 1.
    return [(p,q) for p in g for q in g]+[(x,F(0)),(F(0),x)]


def closed_fixed_state(n, k, outside):
    """Continuous-type reduction gives this exact integer extremal minimum.

    For n<=k, compatible low/high types reduce to pure (k,0)/(n,n),
    or balanced sums floor(3n/2), ceil(3n/2). Endpoint cases include all
    low and all high. This is checked against full integer-type enumeration.
    """
    assert n<=k
    low_sum=3*n//2
    candidates=[outside*(2*k-max(k,low_sum))]
    for lo_sum,hi_sum in [(k,2*n),(low_sum,3*n-low_sum)]:
        d=hi_sum-lo_sum
        for z in {0,outside,max(0,min(outside,d)),max(0,min(outside,d+1))}:
            candidates.append(outside*(2*k-lo_sum)-d*z+z*(z-1)//2)
    return k*k+min(candidates)


def finite_certificate(n,m,k):
    # Growth to equal size k follows from m>k+2n. The final necessary
    # deletion count includes no overlapping terminal/outside edges.
    return (n<=k and k+2*n<m and 2*k<=m and
            closed_fixed_state(n,k,m-2*k)>(2*k-1)*n)


def verify_closed_formula():
    checked=0
    for n in range(1,7):
        for k in range(n,2*n+1):
            for outside in [1,2,3,5,8]:
                exact,_=exact_fixed_state(n,k,outside)
                closed=closed_fixed_state(n,k,outside)
                assert exact==closed,(n,k,outside,exact,closed)
                checked+=1
    return checked


def scaled_minimum(x, c, subdivisions=8):
    """Exact type/support enumeration; floating mixture minimization.

    Finite grids restrict Breaker, so a positive margin is a candidate,
    not a universal certificate for ungridded boards.
    """
    x=F(x)
    y=float(c)-2*float(x)
    if y<0: raise ValueError('No outside vertices')
    types=scaled_types(x,subdivisions)
    low=[t for t in types if not dangerous_pair(t,t,F(1))]
    high=[t for t in types if dangerous_pair(t,t,F(1))]
    best=StateMinimum(float('inf'),(),(),0)
    # Low-low shifts have nonpositive curvature; high-high shifts have zero
    # curvature. Consequently <=1 type from each class suffices globally.
    for lo in low:
        for hi in high+[lo]:
            d0=int(dangerous_pair(lo,hi,F(1)))
            d1=int(dangerous_pair(hi,hi,F(1)))
            linear=y*float(sum(lo)-sum(hi))+y*y*d0
            quadratic=y*y*(d1/2-d0)
            candidates=[0.,1.]
            if quadratic>0:
                candidates.append(max(0.,min(1.,-linear/(2*quadratic))))
            for t in candidates:
                outside_cost=y*(2*float(x)-float(sum(lo)))+linear*t+quadratic*t*t
                margin=float(x*x)+outside_cost-2*float(x)
                if margin<best.margin:
                    best=StateMinimum(margin,tuple(map(float,lo)),tuple(map(float,hi)),t)
    return best


def threshold(x, subdivisions=8):
    lo=max(2*float(x),float(x)+2)
    hi=4.1
    for _ in range(35):
        mid=(lo+hi)/2
        if scaled_minimum(x,mid,subdivisions).margin>0:
            hi=mid
        else:
            lo=mid
    return hi


def brute_check():
    from itertools import combinations_with_replacement
    checked=0
    for n in [1,2]:
        for k in range(n,2*n+1):
            types=degree_types(k,n)
            for outside in range(1,5):
                brute=min(k*k+sum(2*k-sum(t) for t in ts)+
                          sum(dangerous_pair(ts[i],ts[j],n)
                              for i in range(outside) for j in range(i+1,outside))
                          for ts in combinations_with_replacement(types,outside))
                exact,_=exact_fixed_state(n,k,outside)
                assert brute==exact,(n,k,outside,brute,exact)
                checked+=1
    return checked


def main():
    print(json.dumps({'method':'exhaustive degree-grid extremal search',
                      'turn_order':'Breaker first','seed':None,
                      'brute_checked_states':brute_check(),
                      'closed_formula_checked_states':verify_closed_formula()}))
    print('x,candidate_coefficient')
    rows=[]
    for i in range(22,31):
        x=F(i,20)
        c=threshold(x)
        rows.append((c,x))
        print(f'{float(x):.3f},{c:.10f}')
    c,x=min(rows)
    print('best_grid',float(x),c)
    for grid in [4,8,16]:
        candidate=threshold(F(6,5),grid)
        print('grid_refinement',grid,candidate)
    for c in [3.4,52/15,3.5]:
        state=scaled_minimum(F(6,5),c,16)
        print('state',c,state)
    print('finite_equal_states: n,k,m,required_deletions,budget,witness')
    for n,k,m in [(5,6,18),(10,12,35),(20,24,70)]:
        cost,witness=exact_fixed_state(n,k,m-2*k)
        print(n,k,m,cost,(2*k-1)*n,witness)
    print('earlier_coefficient',2+sqrt(3))
    failures=[]
    for n in range(5,10001):
        m=(52*n+14)//15
        k=6*n//5
        if not finite_certificate(n,m,k): failures.append(n)
    print('finite_candidate_check',{'n_range':[5,10000],
          'm':'ceil(52*n/15)','k':'floor(6*n/5)','failures':failures})


if __name__=='__main__':
    main()
