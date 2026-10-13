# Research index

## Target and baseline

Write `L = liminf phi(n)/n` and `U = limsup phi(n)/n`. The objective is a
larger lower bound on `L` and a smaller upper bound on `U`; convergence is a
separate question. The owner confirms the established baseline `2 <= L <= U <= 4`.

| Result | Mathematical status | Repository formalization status |
| --- | --- | --- |
| Matroid lower coefficient 2 | Established by the owner | Argument not yet written here; no endpoint theorem |
| Two-frontier upper coefficient 4 | Established by the owner | Arithmetic and local free-edge bridge written; global strategy unfinished |
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
- `Candidates/Candidate.lean`: target constants 2 and 4; no endpoint proofs yet.

To finish the upper formalization: establish the initial invariant; handle
swapping the smaller terminal side; prove that expansion preserves balance and
the deletion budget; handle a joining edge as immediate victory; apply a
decreasing rank. Then transfer to sufficiently large `m >= (4+eps)n` and the
asymptotic target. The exact-threshold proof and the asymptotic transfer are
distinct obligations.

To finish the lower formalization: first record the owner's matroid argument,
including its bias convention and eventual threshold, then formalize it against
the raw game and prove `BreakerLowerBound 2`.

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
