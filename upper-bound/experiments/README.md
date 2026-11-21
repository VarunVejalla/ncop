# Upper-bound experiments

Research improvements below coefficient `2 + sqrt(3)` for `limsup phi(n)/n` here.
Candidate approaches include longer lookahead, adaptive growth, and sharper
potential or budget arguments. Record the complete adversarial strategy and
eventual threshold before claiming a new endpoint.

The original two-edge lookahead scripts are preserved under
[`research/experiments`](../../research/experiments/README.md).

The new [lookahead experiment](lookahead.py) uses exact, separate threat and
progress budget inequalities. Its [verified strategy argument](../best/lookahead-proof.md)
gives coefficient `2 + sqrt(3)` and is now proved in Lean.

[Longer-lookahead exploration](longer-lookahead.md) records the general
finite-horizon solver, the exploratory three-move candidate `1 + sqrt(6)`,
and additional four- and five-move patterns. None is yet a new endpoint proof.

The [saved 1 + sqrt(6) handoff](sqrt-six-handoff.md) preserves the candidate
strategy, a proposed counting-lemma route, and remaining proof obligations.
Its formalization is deferred; exploring smaller constants is the priority.
