# Asymptotic bounds for the n-cop connection game

On the complete graph `K_m`, fix distinct terminals `s,t`. Each round, the cop
(Breaker) deletes up to `n` free edges, then the robber (Maker) claims one free
edge permanently. Maker wins by claiming an `s-t` path.

Let `phi(n)` be the smallest `m` for which Maker can force a win. The research
objective is to improve lower bounds on `liminf phi(n)/n` and upper bounds on
`limsup phi(n)/n` as `n` tends to infinity. Exact small values are secondary.
We do not assume the ratio converges.

## Current mathematical bounds

```text
2 <= liminf phi(n)/n <= limsup phi(n)/n <= 2 + sqrt(3)
```

Both endpoint predicates are proved in Lean. The lower proof specializes the
matroid strategy of Bednarska and Pikhurko to a partition matroid with a balanced
orientation and two terminal sinks; see
[the formalized lower proof](lower-bound/best/partition-proof.md). The upper
proof grows two balanced terminal trees and creates an unblockable two-move
joining threat; see [the upper proof](upper-bound/best/lookahead-proof.md).

Start with [the research index](docs/research-index.md) for proof status and
remaining obligations.

## Repository map

| Path | Purpose |
| --- | --- |
| [lower-bound/best](lower-bound/best/README.md) | Proved coefficient 2; partition-matroid strategy and source argument |
| [lower-bound/experiments](lower-bound/experiments/README.md) | Attempts to improve the lower coefficient |
| [upper-bound/best](upper-bound/best/README.md) | Proved coefficient 2 + sqrt(3) and lookahead proof map |
| [upper-bound/experiments](upper-bound/experiments/README.md) | Attempts to improve the upper coefficient |
| [research](research/README.md) | Shared methods, component model, and convergence questions |
| [NCop](NCop/) | Shared Lean game definitions and supporting proofs |
| [Candidates](Candidates/) | Public interface for the two proved asymptotic endpoints |
| [docs](docs/research-index.md) | Current status and formalization guides |
| [archive/notes](archive/notes/README.md) | Original notes, preserved verbatim |
| [scripts](scripts/) | Candidate evaluator |

The workstream directories organize research; they are not separate Lake
packages. All existing Lean imports use the root package.

## Build

Install Lean through elan and Python 3.10 or newer. The pinned toolchain is in
`lean-toolchain`; Mathlib is pinned in `lakefile.lean` and `lake-manifest.json`.

```sh
lake exe cache get
lake build NCop Candidates
```

The Python experiments use only the standard library. See
[research/experiments](research/experiments/README.md) before interpreting their
outputs. Simulations do not establish optimal-play bounds.

```sh
python scripts/evaluate_candidate.py
```

`Candidate.lower` and `Candidate.upper` prove the target coefficients 2 and
`2 + sqrt(3)`. The evaluator scores their gap as `sqrt(3)`. During development,
when shared proof
files are intentionally modified, use `--allow-trusted-dirty`; the default
evaluation rejects changes to the trusted tree.

```sh
lake build NCop.ProofAudit
```

The audit prints the axiom dependencies of the upper endpoint and matroid
strategy. These should be only `propext`, `Classical.choice`, and `Quot.sound`.

See [AGENTS.md](AGENTS.md) for research and contribution conventions.
See [GitHub setup](docs/github-setup.md) for the initial commit and remote
creation commands.
The [setup verification record](docs/setup-verification.md) records the initial
setup checks. See [the research index](docs/research-index.md) for subsequent
formalization status.
