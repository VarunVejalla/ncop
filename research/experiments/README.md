# Historical Python experiments

These scripts were moved here without changing their algorithms. They use
Python's standard library and are exploratory, not proof certificates.

| Script | Purpose and limitations |
| --- | --- |
| `ncop.py`, `ncop2.py` | Balanced-component budget calculations with two-edge lookahead; longer lookahead is TODO; not full minimax solvers |
| `fully_random_ncop.py` | Samples random claimed edge sets and measures terminal connectivity; does not model optimal Breaker play |
| `component_random_ncop.py` | Random component-restricted simulation; its loop claims for Maker before deleting for Breaker, unlike the target Breaker-first game |

The two lookahead scripts expose `check(n,m)` and print intermediate states.
The component simulation's main block runs substantial Monte Carlo experiments.
Record seed, parameters, and turn order with any reported experiment. Correct
the turn-order discrepancy before using that simulation to inform the target
game.
