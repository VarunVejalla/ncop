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
