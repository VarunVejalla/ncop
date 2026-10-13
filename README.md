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
2 <= liminf phi(n)/n <= limsup phi(n)/n <= 4
```

The lower bound comes from the owner's matroid formulation; the upper bound
comes from growing two balanced terminal components. These are established
mathematical results reported by the owner, not completed Lean endpoint
theorems in this repository. The matroid proof still needs to be written here;
the two-frontier upper proof has substantial Lean infrastructure.

Start with [the research index](docs/research-index.md) for proof status and
remaining obligations.

## Repository map

| Path | Purpose |
| --- | --- |
| [lower-bound/best](lower-bound/best/README.md) | Established coefficient 2; proof writeup and formalization obligations |
| [lower-bound/experiments](lower-bound/experiments/README.md) | Attempts to improve the lower coefficient |
| [upper-bound/best](upper-bound/best/README.md) | Established coefficient 4 and two-frontier proof map |
| [upper-bound/experiments](upper-bound/experiments/README.md) | Attempts to improve the upper coefficient |
| [research](research/README.md) | Shared methods, component model, and convergence questions |
| [NCop](NCop/) | Shared Lean game definitions and supporting proofs |
| [Candidates](Candidates/) | Unfinished interface for asymptotic endpoint theorems |
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

The evaluator is expected to reject the current candidate because its `lower`
and `upper` theorems are absent. A successful library build alone does not
certify either asymptotic endpoint. CI builds the libraries, not a completed
bound certificate.

See [AGENTS.md](AGENTS.md) for research and contribution conventions.
See [GitHub setup](docs/github-setup.md) for the initial commit and remote
creation commands.
The [setup verification record](docs/setup-verification.md) lists passed checks
and the local Lean build failure that still needs a normal-terminal rerun.
