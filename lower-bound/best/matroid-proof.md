# Matroid application: lower coefficient 2

Status: the asymptotic coefficient is now proved in Lean by the alternative
[partition-matroid argument](partition-proof.md). This document retains the
original graphic-matroid application and its sharper finite range; its
graph-specific steps remain unformalized and are no longer needed for the
asymptotic endpoint.

Source: M. Bednarska and O. Pikhurko, *Biased positional games on matroids*,
European Journal of Combinatorics 26 (2005), 271–285, Theorem 2, pp. 274–275.
[Author-hosted PDF](https://pikhurko.github.io/E/BednarskaPikhurko05ejc.pdf),
[DOI](https://doi.org/10.1016/j.ejc.2003.12.015).
The owner confirmed this is the source of the established lower bound.

## The strategy theorem to formalize

If a loopless matroid's ground set is covered by `q+1` independent sets,
Breaker moving second with bias `q` can keep Maker's set independent.
Maintain independent covering sets that all contain Maker's current set.
After Maker claims `e`, insert it into each covering set. In the set already
containing `e`, no repair is needed. Each other set needs at most one available
element removed, by fundamental-circuit exchange. Delete the union of these
at most `q` elements. The updated independent sets still cover all undeleted
elements and contain all Maker elements. This is the sufficient direction of
the paper's Theorem 2, not an imported Lean axiom.

## Application to the terminal game

Assume `n >= 1`, `m >= 2`, and `m <= 2n+1`. On the first Breaker turn, delete
the direct edge `st`. This costs one of the permitted `n` deletions. Identify
`s` and `t` as one vertex `z`, retaining every other edge as a distinct element.
The resulting loopless multigraph `H` has `m-1` vertices. Its cycle matroid
has as independent sets the forests of this multigraph. A Maker `s-t` path
would become a cycle after identification, so keeping Maker independent in
this matroid suffices to prevent the original winning condition. In particular,
parallel edges cannot be discarded: the two-edge path `s-v-t` becomes a
two-edge cycle.

We next verify that this matroid can be covered by `n+1` independent sets.
Take any edge subset `X` of `H`. Consider its nontrivial connected components.
For one such component with `v >= 2` vertices, its graphic-matroid rank is
`v-1`. If it does not contain `z`, it has at most `v(v-1)/2` edges. If it contains
`z`, it has at most

```text
(v-1)(v-2)/2 + 2(v-1) = (v-1)(v+2)/2
```

edges: ordinary vertices form a simple complete graph, and each has at most
two edges to `z`. Since `v <= m-1`, in either case the component has at most
`(m+1)(v-1)/2` edges. Summing over components gives

```text
2 |X| <= (m+1) rank(X) <= 2(n+1) rank(X).
```

The finite matroid covering theorem (the paper's Lemma 1 with `d=0`) now gives
a cover by `n+1` independent sets. Apply the second-player circuit-prevention
strategy to the remaining game. The first move has already deleted `st`;
Maker now moves first in the residual circuit game, and each subsequent
Breaker move has the full bias `n`. Hence Breaker wins the original game.

## Asymptotic consequence

For every `eps > 0`, take `N=1`. If `n >= N` and `m <= (2-eps)n`, then
`m <= 2n <= 2n+1`, so the preceding strategy applies (and boards with fewer
than two vertices have no terminal pair). This gives `BreakerLowerBound 2`.
Once the threshold function and incompatibility of winning strategies are
formalized, it yields `liminf phi(n)/n >= 2`.

## Lean obligations

The source result and this application are now written out; they are not yet
kernel-checked endpoint theorems. Required components are:

1. A cycle matroid on labeled multigraph edges, preserving parallel edges.
2. The terminal-identification lemma: every terminal path is dependent.
3. The component rank and edge-count inequality above.
4. A finite matroid covering theorem or an explicit independent-set cover.
5. The fundamental-circuit repair strategy, connected to
   `NCop.breakerWinFrom_of_invariant` and the legal initial deletion.
6. `breakerLowerBound_of_linear_wins 2` for the final asymptotic target.
