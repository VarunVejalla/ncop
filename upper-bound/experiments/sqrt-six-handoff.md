# Saved candidate: 1 + sqrt(6)

Saved 2026-10-12. Formalization is deferred at the owner's request; the active
priority is exploration of smaller upper constants.

## Status and intended statement

The established, kernel-checked upper endpoint is `2 + sqrt(3)`. The proposed
improvement `1 + sqrt(6)` is supported by local threat arguments and Python
optimizations, but is not yet a complete written or Lean endpoint proof.
The trusted game remains the two-terminal, Breaker-first game on `K_m`:
Breaker deletes at most `n` free edges, then Maker claims one free edge.
Do not assume convergence of `phi(n)/n`.

The eventual target is: for every positive epsilon, there exists N such that
for every integer n >= N, `phi(n)/n <= 1 + sqrt(6) + epsilon`.
Prefer proving a finite Maker-winning theorem first, with explicit rounding
and additive slack, then use the existing asymptotic interface.

## Candidate strategy and equations

Grow the two terminal trees in balance, checking for a three-Maker-move win
after every Breaker deletion. Stop near component size `k = x*n`, where
`x = sqrt(3/2)`. At `m = c*n`, the number of outside vertices is approximately
`(c-2*x)*n`; it equals `n` at `c = 1 + sqrt(6)`.

Local three-move mechanisms:

- Claim an outside edge to create an auxiliary pair. Its combined terminal
  degrees `(P,Q)` force a two-move win if
  `min(P,Q,max(P-n,0)+max(Q-n,0)) > n`.
- Attach a balanced outside vertex to one terminal, activating adjacent pure
  vertices with more than `n` free edges to the opposite terminal. Joining
  edges and the additional activation-blocking deletions are disjoint.

The apparent worst normalized deletion margins are

```
low:  -3*x*x + (2*c+1)*x - 3*c/2
high: -x*x + 2*x + c*c/2 - 2*c
```

They both vanish at `x=sqrt(3/2)`, `c=1+sqrt(6)`. Eliminating x yields factors
including `c*c-2*c-5`. The low family has total terminal degree `3*n/2`;
the high family has degrees `(n,n)` with its mutual outside edges deleted.

## Possible route to the missing universal counting lemma

This is a proof outline to audit, not an established lemma. At the critical
point there is normalized outside mass 1. Let pure masses be a and b,
`u=a+b`, and balanced mass `z=1-u`. For a balanced type `(p,q)`, subtract
activation costs from its effective retained terminal-degree sum:

```
p+q - I(q>0)*max(0,a+p-1) - I(p>0)*max(0,b+q-1).
```

For fixed pure masses, attempt a mass-shifting reduction to one self-safe
balanced LOW type and one self-dangerous HIGH type. LOW effective sum is at
most 3/2. HIGH effective sum is at most `2-u`. If LOW and HIGH can retain
their mutual outside edges, their actual degree sums add to at most 3;
subtracting activation penalties does not increase this sum.

These bounds suggest the following lower bounds on normalized outside-edge
and terminal-edge deletion cost, relative to `2*x-3/2`:

- All LOW: additional cost at least `u*(3/2-x)`.
- All HIGH: additional cost at least `u*(2-x)-u*u/2`.
- Compatible LOW/HIGH mixture with `u<=1/2`: candidate worst endpoint gives
  additional cost at least `u*(2-x)-u*u`.
- If `u>1/2`, the HIGH effective sum is already at most 3/2.

At `x=sqrt(3/2)` these are nonnegative. Check every reduction, particularly
incompatible LOW/HIGH pairs, zero-coordinate types, and pure-type accounting.
The Python grid does not prove this reduction. If the lemma holds, include
the `x*x` terminal cross-edge cost and compare with the cumulative Breaker
budget. For an epsilon margin, using a subset of n outside vertices plus
terminal deletion costs on extra vertices may handle surplus outside mass;
finite rounding, turn indexing, and balanced growth still require proof.

## Verification and reproduction

- `three_move_search.py`: exact auxiliary-pair optimization, candidate 52/15;
  finite and brute-force checks are recorded by the script.
- `three_move_extended.py`: NumPy degree/density-grid search including pure
  activation; grids suggested `1+sqrt(6)` at `x=sqrt(3/2)`.
- `four_move_optimization.py`: restricted regular-block MILP, seed 414,
  with and without four-move fork constraints. At the critical x,c both
  models returned minimum margin zero. This is supporting evidence only.
- `verify_horizon_solver.py`: 11,664 finite game comparisons passed; it
  verifies finite-horizon game semantics in those cases, not this endpoint.

See [longer-lookahead.md](longer-lookahead.md) for parameters, limitations,
four-move patterns, and reproduction commands.

## Resume exploration below this candidate

Current four-move certificates remove some symmetric and pure/balanced
obstructions, but an asymmetric limiting type `(n/2,n-epsilon*n)` survives
their counting constraints. Search for adaptive or simultaneous four-move
threats on this family and heterogeneous mixtures near it. Test at increasing
bias and outside vertex counts proportional to bias. An exact degree n can
be activated by a single extra edge; a degree `n-epsilon*n` cannot, so avoid
mistaking this boundary artifact for an asymptotic improvement.

The earlier restricted estimate `(2+2*sqrt(17))/3 = 3.41540375...` omitted
this asymmetric family and is not currently supported as a bound. General
minimax can search other first moves and response-dependent continuations;
resource exhaustion must stay unknown. Do not treat surviving these current
certificates as surviving every four-move strategy.
