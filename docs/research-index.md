# Research index

## Target and baseline

Write `L = liminf phi(n)/n` and `U = limsup phi(n)/n`. The objective is a
larger lower bound on `L` and a smaller upper bound on `U`; convergence is a
separate question. The owner confirms the established baseline `2 <= L <= U <= 4`.

| Result | Mathematical status | Repository formalization status |
| --- | --- | --- |
| Matroid lower coefficient 2 | Established by the owner; source and application written | Partition-matroid certificate and complete `BreakerLowerBound 2` proved |
| Two-frontier upper coefficient 4 | Established by the owner | Complete finite strategy and `MakerUpperBound 4` proved |
| Source isolation | Elementary weaker lower strategy | Supporting lemmas written; no final asymptotic theorem |

The original notes record an older `n <= phi(n) <= 4n` baseline. They predate
the owner's clarification about the matroid lower bound and are historical.

## Lean proof map

- `NCop/Game.lean`: raw board, legal moves, reachability, and force-win predicates.
- `NCop/Target.lean`: epsilon/eventually predicates `BreakerLowerBound c` and
  `MakerUpperBound c`, intended to express the asymptotic bounds.
- `NCop/Counting.lean`, `NCop/CutPairs.lean`: finite support, deletion budgets,
  pigeonhole arguments, and ordered cut-pair counting.
- `NCop/Lemmas.lean`: validity, source avoidance, and reachability helpers.
- `NCop/FourNArithmetic.lean`, `NCop/TwoFrontier.lean`: the strict cut-size versus
  total-deletion-budget inequality at `m = 4n`.
- `NCop/Frontier.lean`, `NCop/TwoFrontierRaw.lean`: free progress edge after
  any legal Breaker deletion, conditional on the balanced numerical invariant.
- `NCop/StrategyCriterion.lean`: decreasing-rank criterion for a global Maker win.
- `NCop/InvariantStrategy.lean`: invariant-to-winning-strategy theorems for both
  players, with free-edge count supplying termination automatically.
- `NCop/Asymptotic.lean`: finite linear winning bounds imply the epsilon/eventually
  asymptotic target predicates.
- `NCop/BalancedTrees.lean`: explicit terminal-tree invariant, initialization,
  expansion, side swapping, and complete finite Maker strategy for `m >= 4n`;
  concludes `makerUpperBound_four`.
- `NCop/MatroidRepair.lean`: fundamental-circuit repair outside protected Maker
  edges, derived from Mathlib's matroid API.
- `NCop/MatroidStrategy.lean`: complete independent-cover repair and Breaker
  strategy; `MatroidLowerCertificate` isolates the graph-specific obligations.
- `NCop/PartitionSafety.lean`: an injective outgoing-tail map with terminal
  sinks prevents a terminal path; an explicit fiber coloring gives a
  partition-matroid certificate.
- `NCop/BalancedOrientation.lean`: parity tournament, terminal overrides, and
  fiber-injective colors using `ceil(m/2)+2` colors.
- `NCop/LowerBound.lean`: Breaker wins for `m+4 <= 2n`, then concludes
  `breakerLowerBound_two` by choosing `N >= 4/eps`.
- `NCop/ProofAudit.lean`: axiom-dependency reports for the upper endpoint and
  the general matroid strategy.
- `Candidates/Candidate.lean`: constants 2 and 4; both `lower` and `upper` are
  proved against the exact target predicates.

The upper formalization now handles every step above directly at `m >= 4n`.
It does not require embedding a `4n`-vertex subgame into a larger board.

The lower endpoint is complete using an explicit partition matroid instead of
a cycle matroid. Its finite bound has additive slack, deliberately immaterial
for the asymptotic goal. See
[the formalized application](../lower-bound/best/partition-proof.md) and
[the formalization framework](formalization-framework.md). The original
[graphic-matroid argument](../lower-bound/best/matroid-proof.md) remains a
written alternative; formalizing its sharper finite range is optional.

The old [four-n plan](four_n_upper_bound_lean_plan.md) provides background;
its cut-cardinality TODO has been addressed by the ordered cut-pair bridge.
See also [the evaluator guide](lean_research_setup.md).

## Research leads

- Lower-bound improvements: stronger Breaker strategies, matroid refinements,
  and potential or counting methods.
- Upper-bound improvements: longer lookahead, adaptive component growth,
  improved potentials, LP relaxations, conductance/resistance, and overlap
  counting of remaining winning paths.
- Shared questions: exact component-game descriptions and whether the
  asymptotic ratio converges.

These are leads, not improved proved constants. Python experiments are indexed
in [research/experiments](../research/experiments/README.md).
