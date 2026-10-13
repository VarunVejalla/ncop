# Established upper bound: coefficient 4

The owner has proved `limsup phi(n)/n <= 4` by balanced two-frontier growth.

Maker maintains two disjoint claimed trees rooted at the terminals, growing
the smaller unless a free joining edge wins immediately. After `r` expansions,
their sizes sum to `r+2` and differ by at most one. For smaller size `S`, there
are `S(m-S)` edges leaving that component and none are already Maker-claimed.
At `m=4n`, the arithmetic proof gives `S(m-S) > (r+1)n` for `r <= m-2`.
Breaker therefore cannot block all progress edges with its total deletion
budget. Expansion eventually exhausts unused vertices, forcing a joining edge.

The complete strategy, including initialization, invariant preservation,
side swapping, and termination, is proved in `NCop/BalancedTrees.lean`:

```lean
NCop.makerWins_of_four_mul_le
NCop.makerUpperBound_four
Candidate.upper
```

The finite theorem covers every `m >= 4n`, `n >= 1`. The asymptotic theorem
proves the exact epsilon/eventually predicate `NCop.MakerUpperBound 4`.
See [the research index](../../docs/research-index.md) and the axiom audit
`lake build NCop.ProofAudit`.
