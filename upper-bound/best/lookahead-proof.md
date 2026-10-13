# Extra lookahead: coefficient 2 + sqrt(3)

Status: complete written strategy and kernel-checked finite and asymptotic
endpoint theorems in `NCop.LookaheadStrategy`. The finite theorem is
`makerWins_of_two_add_sqrt_three_mul_le`; the asymptotic endpoint is
`makerUpperBound_two_add_sqrt_three`. Both use the trusted Breaker-first game.

## Strategy and disjoint accounting

Breaker deletes at most n free edges first each round, then Maker claims one.
Maker maintains two terminal trees A,B, of sizes a<=b<=a+1; all outside
vertices remain Maker-isolated. Before Maker moves, Breaker's total deletion
budget is (a+b-1)n, since Maker has claimed a+b-2 edges.

Maker first takes any free A-B edge. Otherwise, if some outside vertex has
a free attachment to one side and more than n free edges to the other,
Maker attaches it to the first side. Breaker cannot delete all joining edges
next round, so Maker wins on the following move. Otherwise Maker grows the
smaller terminal tree. We prove such growth is available until a win is forced.

If no immediate win exists, all ab joining edges are deleted. For an outside
vertex with free degrees p,q into A,B, no two-move win means neither
(p>0 and q>n) nor (q>0 and p>n). Thus either p=0, q=0, or both p,q<=n.
The minimum deletions required at that vertex are exactly

    d(a,b) = min(a,b,max(a-n,0)+max(b-n,0)).

These edges are disjoint across outside vertices and from A-B edges.
Absence of either winning test therefore requires

    ab + (m-a-b)d(a,b) <= (a+b-1)n.                 (1)

Separately, preventing smaller-side progress requires deletion of its whole
boundary: a(m-a) edges. Progress follows if

    a(m-a) > (a+b-1)n.                            (2)

These two deletion counts overlap; do not add them. In particular, the
historical ncop2.py progress subtraction cannot justify adding both costs.

## Optimization and complete asymptotic argument

At a=b=k with n<k<=2n, the left side of (1) is
k^2+2(m-2k)(k-n). Write k/n -> x in (1,2) and m/n -> c.
Its excess over the budget, divided by n^2, tends to

    -3x^2 + 2(c+1)x - 2c.

This is positive when

    c > (3x^2-2x)/(2x-2)
      = 3x/2 + 1/2 + 1/(2(x-1)).

The minimum is 2+sqrt(3), attained at x=1+1/sqrt(3).

Fix epsilon>0, let c=2+sqrt(3)+epsilon, and choose
k=ceil((1+1/sqrt(3))n). For all sufficiently large n, k<=2n and every
m>=cn satisfies m>k+2n. At each balanced state before (k,k), a<=k and
a+b-1<=2a, so a(m-a)>2an>=(a+b-1)n. Thus (2) guarantees legal growth
unless a winning test already succeeds. At (k,k), the normalized excess
in (1) tends to a strictly positive number; rounding contributes only O(n).
The excess increases with m, so (1) fails on every larger board too.
Maker therefore wins by the immediate or two-move test by this stage.

For every epsilon>0, this gives N such that for every n>=N and every integer
m>=(2+sqrt(3)+epsilon)n, Maker wins against every legal Breaker strategy.
Hence limsup phi(n)/n<=2+sqrt(3), without assuming convergence.

## Sharper finite arithmetic for formalization

The exact `(2k-1)n` budget gives a finite theorem without epsilon slack.
Put `s=sqrt(3)`, `x=1+s/3`, and `k=floor(x*n)`. For `n>=4` and
`m>=(2+s)n`, we have `n<=k<=2n` and `m>k+2n`. The exact excess equals

    k^2 + 2(m-2k)(k-n) - (2k-1)n
      = n - 3(k-x*n)^2 + 2(m-(2+s)n)(k-n).

The squared rounding error is at most 1, and the last term is nonnegative.
The excess is therefore at least `n-3>0`. Thus the same complete strategy
wins for every `n>=4` and integer board size `m>=(2+sqrt(3))n`.

## Python verification, 2026-10-12

Run `python upper-bound/experiments/lookahead.py`. Deterministic; no seed.
It exhaustively checks the local degree formula for n=1..4 and a,b=1..8,
then uses exact integer inequalities for the balanced strategy certificate.
It is neither random play nor full minimax. Failure is inconclusive.
For n=100,1000,10000, the smallest certified boards are 373,3732,37320.
These are sufficient board sizes, not claimed exact values of phi(n).

Lean verification on 2026-10-12: `lake build NCop Candidates NCop.ProofAudit`
passed (3319 jobs). The complete finite theorem and asymptotic endpoint audit
to only `propext`, `Classical.choice`, and `Quot.sound`. The candidate evaluator
accepted `C1=2`, `C2=2+Real.sqrt 3`, with gap `1.7320508075688772`.
