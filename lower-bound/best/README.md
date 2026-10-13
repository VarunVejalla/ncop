# Established lower bound: coefficient 2

The asymptotic lower endpoint is proved in Lean via a partition-matroid
specialization of the circuit-game strategy of Bednarska and Pikhurko (2005).
See [the formalized argument](partition-proof.md).

```lean
NCop.breakerWins_of_add_four_le_two_mul
NCop.breakerLowerBound_two
Candidate.lower
```

The finite theorem proves Breaker wins when `m+4 <= 2n`; the additive slack
disappears in `BreakerLowerBound 2`. The orientation's partition-matroid cover
and terminal safety are explicit, so no general graphic-matroid covering
theorem is needed. Source isolation is a weaker fallback.

The owner's original terminal-identification argument, with the sharper finite
range `m <= 2n+1`, remains a written mathematical alternative in
[matroid-proof.md](matroid-proof.md); that alternative has not been formalized.
