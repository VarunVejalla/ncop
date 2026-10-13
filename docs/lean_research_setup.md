# Lean Research Scaffold

Current status is recorded in [research-index.md](research-index.md). The
established mathematical target coefficients are now 2 and 4. This guide's
source-isolation proof is a preliminary formalization milestone, not the best
known lower bound. The candidate now proves both `lower` for coefficient 2
and `upper` for coefficient 4. The preliminary milestones below are historical.

This repository separates the immutable problem statement from the file that
agents are expected to mutate.

## Trusted Core

The trusted core lives in `NCop/`.

* `NCop/Game.lean` defines the two-terminal Maker-Breaker game on `K_m`.
* `NCop/Target.lean` defines the asymptotic target predicates:
  * `BreakerLowerBound C1`
  * `MakerUpperBound C2`

The candidate should prove those exact predicates. Do not let automated agents
edit `NCop/`, `lakefile.lean`, or `lean-toolchain` unless the task is explicitly
to improve the formalization itself.

## Candidate Interface

The evolved file is `Candidates/Candidate.lean`.

It should eventually expose:

```lean
namespace Candidate

def C1 : ℝ := 2
def C2 : ℝ := 4

theorem lower : NCop.BreakerLowerBound C1 := by
  ...

theorem upper : NCop.MakerUpperBound C2 := by
  ...

end Candidate
```

Agents may add any helper definitions and lemmas in the candidate file. The
score is based on the numerical gap `C2 - C1` once both theorems compile. The
evaluator currently understands integer/rational arithmetic and simple square
roots such as `2 + Real.sqrt 3`.

## Evaluator

Run:

```powershell
python scripts\evaluate_candidate.py --allow-trusted-dirty
```

During normal automated runs, omit `--allow-trusted-dirty`; that makes the
script reject candidates if trusted files are modified.

The evaluator currently:

* parses supported real constants `C1` and `C2`;
* requires theorem names and target types;
* rejects common proof escape hatches such as `sorry`, `admit`, `axiom`,
  `constant`, and `unsafe`;
* runs `lake build Candidates` when `lake` is available;
* returns the score `C2 - C1` for valid candidates.

## First Formal Proof Target

The easiest first lower-bound proof is source isolation:

If `n >= m - 1`, Breaker deletes every edge touching the source terminal on the
first move. Maker can never claim an edge incident to the source, so Maker never
creates an `s-t` path. This should yield `BreakerLowerBound 1`.

After that, the matroid-circuit proof should be formalized to reach
`BreakerLowerBound 2`.
