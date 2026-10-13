# Lower coefficient 2 via a partition matroid

This specializes the independent-cover strategy from Bednarska and Pikhurko,
*Biased positional games on matroids* (2005), Theorem 2. That strategy is proved
locally in `NCop.MatroidStrategy`; no paper theorem is assumed as an axiom.
The partition construction below is an alternative to the terminal-identified
cycle matroid described in [matroid-proof.md](matroid-proof.md).

## Orientation and colors

For distinct vertices `u,v`, orient the edge from the smaller label to the
larger if their labels have the same parity, and reverse it otherwise. For
any fixed tail `u`, outgoing neighbors have distinct values `floor(v/2)`:
two vertices with the same half-index are consecutive and of opposite parity,
so they cannot both be outgoing neighbors of `u`. There are at most
`ceil(m/2)` such half-indices.

Override the orientation on edges incident to a terminal so those edges point
into that terminal. Delete the direct `st` edge on the first Breaker move.
Every remaining edge now has an ordinary tail. Retain the half-index colors
for edges between ordinary vertices and reserve two extra colors for edges
into `s` and `t`. Thus there are `ceil(m/2)+2` colors, and each color has at most
one outgoing edge at each vertex.

## Partition matroid and terminal safety

Pull back the free matroid on the ordinary vertices along the tail map.
Its independent edge sets have ordinary tails and at most one edge per tail.
Each color class is independent, and the classes cover every edge left after
the opening deletion.

Independence prevents a terminal path. Indeed, each vertex in the claimed
graph has at most one outgoing edge; let `next(v)` be its claimed edge's head,
or `v` if there is no outgoing edge. Both terminals are fixed points of `next`.
Along a claimed undirected edge, the property "some iterate of `next` reaches
`t`" propagates in either direction. Reverse propagation adds one iterate;
forward propagation removes one, since the edge's tail cannot equal `t`.
Consequently an `s-t` path would imply that some iterate starting at the fixed
point `s` reaches `t`, contradicting the distinctness of the terminals.

Cycles away from the terminals are harmless. This proof does not need Maker's
whole graph to remain a forest.

## Finite and asymptotic bounds

If `m+4 <= 2n`, then `ceil(m/2)+2 <= n+1`, and `n >= 1`. Embed the explicit
colors in `Fin (n+1)`. The independent-cover strategy can repair all color
classes after every Maker move using at most `n` free deletions. Together with
the legal opening deletion this proves `BreakerWins m n`.

For any `eps > 0`, choose an integer `N >= 4/eps`. If `n >= N` and
`m <= (2-eps)n`, then `eps*n >= 4`, hence `m+4 <= 2n`. This proves precisely
`NCop.BreakerLowerBound 2`. The finite slack is intentionally secondary to the
asymptotic coefficient.

## Lean map

- `NCop.PartitionSafety`: terminal-path exclusion and the partition-matroid
  certificate assembled from a sink orientation and fiber colors.
- `NCop.BalancedOrientation`: parity orientation, half-index injectivity,
  terminal overrides, and the explicit independent-cover colors.
- `NCop.LowerBound`: finite strategy theorem and asymptotic endpoint.
- `Candidates.Candidate`: public endpoint interface.
