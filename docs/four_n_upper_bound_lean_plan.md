# `MakerUpperBound 4` Lean Plan

Status update: the ordered cut-pair bridge in `NCop.CutPairs` and
`NCop.Frontier` now addresses the cut-counting obstacle below, and
`NCop.TwoFrontierRaw` contains the conditional local progress theorem.
The global strategy and asymptotic endpoint remain unfinished; see
[research-index.md](research-index.md) for the current proof map.

Goal:

```lean
theorem upper : NCop.MakerUpperBound 4 := by
  ...
```

Informal strategy: Maker maintains two disjoint claimed connected sets `S` and
`T`, initially the source and target. On Maker's `k`th move, after Breaker's
`k`th deletion move, Maker expands the smaller set by claiming a free edge from
that set to an unused vertex. If no such edge exists but a free edge joins the
two sets, Maker claims it and wins.

The proof should be organized around these lemmas.

## State Invariant

After `k` Maker moves, unless Maker has already won:

* Maker's claimed graph contains a connected component `A` containing source.
* Maker's claimed graph contains a connected component `B` containing target.
* `A` and `B` are disjoint.
* `|A| = floor((k + 2) / 2)` and `|B| = ceil((k + 2) / 2)`, up to the exact
  indexing convention.
* All vertices in `A ∪ B` were acquired by Maker's expansion moves.
* Breaker has deleted at most `k * n` edges total.

## Progress Lemma

Assume `A` and `B` are disjoint and connected through Maker edges, and Breaker
has deleted at most `k * n` edges.

Let `A` be the smaller component. If Maker has not already won, then either:

* there is a free edge from `A` to `B`, so Maker wins immediately; or
* there is a free edge from `A` to an unused vertex, so Maker expands `A`.

The core counting inequality should be phrased as:

```text
candidate edges from A to (unused ∪ B)
  = |A| * (m - |A|)
```

Breaker can block at most `k * n` of these by deletion, and Maker has claimed
only the tree edges already used to build the two components. For the basic
`4n + o(n)` proof, choose a stopping time around `k = m - o(m)` and use the
fact that the minimum relevant product is asymptotically `m^2 / 4`.

## Finish Lemma

Once `|A|` and `|B|` are both near `m / 2`, the number of edges between them is
asymptotically `m^2 / 4`. If `m >= (4 + eps) n` and `n` is large, this exceeds
the total number of Breaker-deleted edges plus the already claimed Maker edges,
so some edge between `A` and `B` is free.

## Formalization Notes

The current formalization now has a proof-friendly wrapper:

* `NCop.TwoFrontier.TwoFrontierState` stores the numerical invariant
  `(m,n,r,S,T)` from the markdown proof.
* `TwoFrontierState.sourceChoices_gt_deletedBudget_four_mul` proves the
  arithmetic heart of the `4n` proof:

```lean
st.deletedBudget < st.sourceChoices
```

whenever `m = 4n`, `n >= 1`, and `r <= m - 2`.

This proof still needs a bridge from the numerical wrapper to the raw game:

* a `Fintype`/`Finset` representation of all edges;
* cardinality of edges touching a vertex;
* cardinality of edges between two disjoint vertex sets;
* monotonicity of `AtMost`;
* a pigeonhole lemma: if a candidate edge set has cardinality larger than the
  union of deleted and already-claimed forbidden edges, then it contains a free
  edge.

Most of this bridge now exists in `NCop.Counting`, `NCop.Lemmas`, and
`NCop.Frontier`. The main remaining raw-game bridge is:

```lean
(B.reachableFinset s).card * (m - (B.reachableFinset s).card)
  <= (B.sourceFrontier s).card
```

Once that cut-cardinality lemma is proved, the local progress theorem in
`NCop.Frontier` can turn the two-frontier numerical inequality into a free edge
for Maker.
