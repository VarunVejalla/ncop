# Longer-lookahead exploration

These are local threat results and exploratory optimizations, not new endpoint
theorems. The proved upper endpoint remains `2 + sqrt(3)`. The game is
Breaker-first with bias `n`; local positions below are immediately after
Breaker's deletion, with Maker to move.

## General finite-horizon method

`horizon_solver.py` contracts every Maker component, retains the number of free
edges between components, and evaluates the alternating game tree. A Maker move
contracts two components; a Breaker move deletes at most `n` free edges.
Increasing the horizon changes a parameter rather than the game model.
Terminal joins and the exact two-move blocking cost provide pruning; a sound
four-move certificate is optional. Completed negative results mean no win
within the specified horizon, not no eventual win. Resource exhaustion returns
unknown, never a negative result.

`verify_horizon_solver.py` compares against an independent original edge-mask
solver, including all Breaker deletions of size at most the bias. All 11,664
comparisons passed: every one of the 729 edge states on `K_4`, biases 1 and 2,
horizons 1 through 4, and both player phases. This verifies these finite cases,
not an asymptotic theorem.

## Three-move candidates

`three_move_search.py` studies building an auxiliary pair. Its deletion-count
optimization suggests `52/15`. `three_move_extended.py` adds threats obtained
by attaching a balanced vertex next to vertices with more than `n` free edges
to one terminal component. Its finite degree/density grids suggest the smaller
candidate `1 + sqrt(6) = 3.4494897428...`, with component size
`sqrt(3/2) n` and approximately `n` outside vertices.

The two apparent extremal deletion margins, with `k=x n` and `m=c n`, are

```
-3*x*x + (2*c+1)*x - 3*c/2
-x*x + 2*x + c*c/2 - 2*c
```

They meet at `x=sqrt(3/2)`, `c=1+sqrt(6)`. These are independently derived
candidate equations. A grid minimum does not establish a universal minimum
over all heterogeneous positions. A complete counting argument, finite
rounding estimates, and a strategy against optimal play are still required
before claiming `forall epsilon > 0, eventually phi(n)/n <= c + epsilon`.

## A four-move threat missed at three moves

Write `d(P,Q)=min(P,Q,max(P-n,0)+max(Q-n,0))`. For a free outside edge `uv`,
let `P,Q` be its combined free degrees into the terminal components. After
Maker claims `uv`, Breaker must spend at least `d(P,Q)` deletions to neutralize
the resulting two-move threat.

A third outside vertex `w` is robust when the combined terminal degrees of
`u,v,w` satisfy

```
P_total > 2*n, Q_total > 2*n, P_total + Q_total > 4*n.
```

After any next Breaker deletion, claiming a surviving edge from the auxiliary
pair to such a vertex produces a component with blocking cost greater than
`n`. Thus Breaker must also delete every pair-to-robust-vertex free edge.
Those deletions are disjoint from the terminal-edge deletions above. If their
number plus `d(P,Q)` exceeds `n`, Maker wins within four moves.

For any positive `n` divisible by four, three outside vertices each having
`3*n/4` free edges to each terminal, with a free two-edge path among them,
satisfy this certificate: pair cost is `n` and one boundary edge remains to
be blocked. This persists at arbitrarily large bias. With only these three
outside vertices it has no three-move win. Exact minimax, with the certificate
shortcut disabled, verifies the triangle examples at biases 4, 8, 12 and 24.
The certificate was also checked directly at bias 1000 on the path.

This removes an obstruction that appeared in the three-move optimization.
It is evidence that a further improvement is plausible, not a numerical
asymptotic bound: count how many deletions avoiding all such patterns forces.

## Longer searches and reproduction

### Incorporating the fork constraints: regular-block optimization

`four_move_optimization.py` uses SciPy's MILP solver to maximize retained
outside-edge density for a fixed degree-type distribution. Edge densities
are continuous; binary gates decide whether a type pair has free edges.
It includes dangerous-pair exclusions, pure-vertex activation constraints,
robust-triple boundary constraints, and optionally the new aggregate fork
constraints. Comparing the same distributions with and without forks isolates
their effect. Vertex degrees and counts are normalized by the bias.

This is a restricted ansatz: every vertex in a type has the same retained
degree into every other type, and distributions are sampled, not exhaustively
optimized. A positive margin is therefore not a universal endpoint proof.
The sampled positions need not be reachable through the proposed strategy.
MILP presolve is disabled: with presolve enabled the installed solver reported
infeasibility on a problem whose all-zero assignment is feasible.

Parameters: seed 414, 60 random two-balanced-type/two-pure-type mixtures per
parameter pair, three explicit fork mixtures, and uniform benchmark families;
`x` in `{1.04103520853922,1.125,1.2,sqrt(1.5),1.25}` and `c` in
`{3.4,3.41540375041177,3.45}`, plus a check at `c=1+sqrt(6)`.
Each MILP has a two-second limit; unsuccessful solves raise an error rather
than being interpreted as evidence of a bound.

Result: fork constraints improve deletion margins for 26--34 sampled
distributions per parameter pair, but do not improve the worst margin.
An asymmetric benchmark with terminal degrees approaching `(n/2,n)` from
below is unaffected by both the robust-triple and fork constraints. It
restores the old low-family margin

```
-3*x*x + (2*c+1)*x - 3*c/2.
```

Together with the uniform-high family it still obstructs this detector model
below `1+sqrt(6)`. Thus the earlier `3.4154` estimate from just the symmetric
two-thirds and uniform-high families was too optimistic. This conclusion is
about the present constraints, not about all four-move strategies.

The saturated coordinate is interpreted as a limit from below, not a literal
integer degree `n`: exactly at `n`, one extra adjacency can activate a threat,
whereas at `n-epsilon*n` it cannot. Dropping this distinction can spuriously
improve an asymptotic grid estimate. The next useful search target is a new
four-move certificate that handles these asymmetric near-saturated vertices.

### An adaptive fork missed by the robust-triple test

The seeded search `four_move_search.py` found this configuration at bias 4:
outside degrees `(0,5)`, `(4,1)`, `(4,3)`, with free edges joining the middle
vertex to the other two. It has no three-move win, but an exact four-move win.
Multiplying terminal degrees and bias by 2, 3, 4, 8 and 16 preserves both
results in exact minimax. The original robust-triple detector misses it.

Here is a complete local argument for every positive `n` divisible by four.
Let `u=(n,n/4)`, `v=(n,3n/4)`, `w=(0,5n/4)`, with free edges `uv` and `uw`.
Maker first claims `uv`, creating a component `C` with degrees `(2n,n)`.
To prevent an immediate two-move connection threat, Breaker must spend its
whole budget on one of exactly two responses:

1. Delete all `n` second-terminal edges of `C`. Maker claims `Cw`, producing
   degrees `(2n,5n/4)`. Its two-move blocking cost exceeds `n`, so Maker wins
   in two further moves against any next deletion.
2. Delete `n` first-terminal edges of `C`, leaving degrees `(n,n)`. Maker
   attaches `C` to the first terminal. Breaker must delete the resulting `n`
   joining edges, using its whole next budget. The surviving edge `Cw` now
   attaches `w` to that terminal, with `5n/4 > n` winning edges to the other.
   Maker attaches `w` and then joins the terminals.

For any partial split between the two terminal directions, `C` retains more
than `n` first-terminal edges and a positive second-terminal degree, already
giving a two-move win. Consequently the two listed responses are exhaustive.
This is an adaptive four-move threat, not merely an unconditionally robust
triple. `four_move_patterns.py` implements the sufficient certificate with
pair degrees at least `(2n,n)` and an adjacent pure opposite-terminal vertex
of degree greater than `n`. It also covers swapped terminals.

This proves a scalable local improvement in detection. It does not by itself
lower the numerical endpoint: a new global deletion-count optimization must
include these fork constraints alongside the robust-triple constraints.

The detector also implements a stronger aggregate version. A pair with
degrees `(P,Q)`, `P>=2n`, `0<Q<=n`, wins within four moves if

```
Q + sum_w min(number_of_free_pair_w_edges, degree_to_second_terminal(w)-n) > n,
```

where the sum is over pure second-terminal neighbors of degree greater than
`n`. To neutralize the pair, Breaker either deletes its whole `Q`-fiber, or
spends at least `n` reducing `P` to `n`. In the first case each further
deletion reduces the sum by at most one, so a pure neighbor remains available
to merge into the pair and force a two-move win. The second case is possible
only at `P=2n`, uses the entire budget, and leaves the sum untouched. Maker
attaches the pair to the first terminal; the next Breaker needs `Q` joining
deletions plus the displayed sum to neutralize all activated pure neighbors.
Their edge sets are disjoint, so the budget is insufficient. This aggregate
form can matter when both terminal components have size only slightly above
`n`: it does not require a pure vertex of degree as large as `5n/4`.

Run from this directory:

```
python verify_horizon_solver.py
python three_move_search.py
python three_move_extended.py
python longer_horizon_search.py
python four_move_search.py
python four_move_optimization.py
```

The first, second, and fourth scripts use the standard library; the extended
optimization requires NumPy. Search parameters and limits are printed as JSON.
The horizon sweeps are deterministic without randomness; the discovery and
MILP distribution searches use the recorded seeds 413 and 414. The larger-component sweep
uses 4 and 5 outside vertices, biases 2, 3 and 4, symmetric terminal degrees
`floor(n/2)`, `floor(2*n/3)`, and `floor(3*n/4)`, horizons 3 through 6, and
stops at the first win. Per-case limits are 15,000 states, 60,000 responses,
and one second. No symmetry restriction is imposed on the players' moves.

One example first wins at five moves: bias 2, four outside vertices with one
edge to each terminal and a complete free outside graph. It loses within four
moves and wins within five. At bias 4, the analogous doubled terminal degrees
do not win within six moves. This particular five-move example therefore does
not itself supply a scalable asymptotic improvement.

The reusable research pipeline is: exact horizon solver, extract threat
certificates, prove a global deletion lower bound for positions avoiding all
certificates, then insert that bound into the balanced-growth strategy and
prove the eventual endpoint. The solver extends immediately to longer
horizons; the global extremal counting is the substantial remaining step.
