# Project guide

## Objective

Improve the constants in lower bounds on `liminf phi(n)/n` and upper bounds on
`limsup phi(n)/n` for the two-terminal, Breaker-first game on `K_m`.
The established mathematical baseline is 2 and 4. Small-n values are secondary;
do not assume a limit exists. Start with `docs/research-index.md`.

## Research conventions

- Distinguish owner-established mathematics, complete written proofs,
  kernel-checked endpoint theorems, supporting lemmas, and conjectures.
- The matroid lower bound 2 is established according to the owner, but its proof
  is not yet recorded here. Do not invent the missing argument or downgrade the
  baseline to the older source-isolation coefficient 1.
- A simulation, local progress lemma, or proposed constant is not an endpoint
  proof. Trace improvements through a complete strategy against optimal play.
- State the turn order and asymptotic quantifiers in every bound argument.
- Keep exploratory work in the relevant `experiments` directory. Promote to
  `best` only with a complete argument and a clear verification record.
- Preserve original notes under `archive/notes`; update current documentation
  instead of rewriting the historical record.

## Code and verification

- The root Lake package is shared. Keep `NCop` and `Candidates` module paths
  stable unless a reorganization is explicitly requested.
- `NCop/Game.lean` and `NCop/Target.lean` are the trusted problem statement.
  Do not weaken definitions to make a candidate pass. Changes to the trusted
  model require an explicit formalization task and a documented justification.
- Do not add `sorry`, axioms, `admit`, unsafe proof escapes, or trust extensions.
- Check affected Lean targets and report what was actually verified. A library
  build does not prove missing endpoint theorems.
- Do not run `lake clean` or commit `.lake`, generated results, credentials,
  machine-specific agent settings, or scratch files.
- Keep experiments reproducible: record parameters, seed, turn order, and
  whether a method is exhaustive, heuristic, random, or adversarial.
- Use `AGENTS.md` as the canonical instructions for all coding agents.
- Do not push or publish unless authorized by the user.

## Map

`lower-bound/` and `upper-bound/` contain endpoint notes and experiments;
`research/` contains shared methods; `NCop/` contains shared Lean proofs;
`Candidates/` contains the endpoint interface; `docs/` contains current status;
`archive/notes/` contains historical notes; `scripts/` contains maintenance tools.
