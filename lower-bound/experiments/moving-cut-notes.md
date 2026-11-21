# Moving cuts and threat repair: first lower-bound exploration

Date: 2026-10-12. No improved asymptotic lower endpoint is proved. The
owner-established and kernel-checked coefficient remains 2. The purpose is
to seek a delta > 0 with, for every epsilon > 0, eventually
`phi(n)/n >= 2+delta-epsilon`, not merely improve a finite additive term.

## Game, policies, and verification method

Breaker moves first on `K_m`, deletes at most bias n free edges, and Maker
claims one free edge. `moving_cut.py` contracts Maker components, retaining
parallel free-edge counts and original component sizes. Breaker first deletes
all free edges joining the terminal components. More than n such edges is an
unavoidable loss. If a free separating cut can be deleted with the remaining
budget, Breaker closes it and wins. Otherwise it spends its budget according
to a cut policy:

- `mincut`: target the smallest free separating cut.
- `regularized_density`: minimize `(free_cut_capacity+n)/(|S|*|T|)`.
- `balanced`: minimize `free_cut_capacity-1.1*|S|*|T|`.
- `density_r`: vary the regularization term to `r*n`.

These cuts are unions of Maker components, so no claimed edge crosses them.
Exact cut enumeration groups true-twin components: this removes equivalent
partitions, not distinct capacities. Default deletion priority is a heuristic
based on terminal incidences and free degrees. All deletions are legal.

The verifier searches every component-merging Maker move, to the end of the
game, against the specified fixed policy. For the original edge game, the
policy explicitly passes after any Maker claim internal to a component. This
extends the contracted policy legally and makes ignoring such claims sound.
Each case has a 50,000-state and three-second limit. Exceeding either returns
unknown, not a Breaker win. Searches are deterministic, with no random seed.

An optional AND/OR search lets Breaker choose adaptively from seven policy
responses on each turn. Failure of this restricted menu is not failure of
optimal Breaker play. Its positive conclusions still cover every Maker move.

## Repair refinement

For a board immediately after Breaker deletion, compute the maximum, over
every possible next Maker contraction, of the exact deletion cost required
to neutralize all two-Maker-move threats. For terminal degrees `(p,q)`, the
cost per outside component is

```
min(p,q,max(p-n,0)+max(q-n,0)).
```

Add current joining edges, which must also be deleted. If the maximum exceeds
n, some next Maker move forces a win within three Maker moves. This quantity
is a useful exact local risk score, but controlling it for one turn does not
establish an invariant strategy.

`*_repair` greedily minimizes that score while deleting within the selected
cut. `global_repair` permits off-cut deletions when they reduce the risk more.
This is the useful refinement: restricting all repairs to one cut was too
rigid. `global_swap` tries improving the completed batch by one-edge swaps.
`global_batch` enumerates up to 2,000 legal batches if the greedy board still
admits a three-move win, and uses the first batch reducing the risk to at most
n. This truncation defines a heuristic Breaker policy; exhaustive Maker
verification against it remains exhaustive when completed.

## Results

| Bias n | Board m | Cut-only policies | Global repair |
| --- | --- | --- | --- |
| 2 | 6 | All three fail | Wins against every Maker continuation |
| 3 | 8 | All three fail | Wins against every Maker continuation |
| 4 | 10 | Regularized density wins | Wins against every Maker continuation |
| 5 | 12 | Regularized density wins | Unknown at the four-second test limit |
| 3 | 9 | Tested variants fail | Explicit Maker counterexample |
| 4 | 11 | Tested variants fail | Explicit Maker counterexample |
| 5 | 13 | Tested variants fail | Explicit Maker counterexample |
| 6 | 15 | Some variants fail; others unknown | Unknown at tested limits |

The finite successes have `m=2n+2`, one vertex beyond the owner's written
graphic-matroid sufficient range `m<=2n+1`. They do not imply a coefficient
larger than 2. In particular ratios 3, 8/3 and 5/2 at small biases should not
be extrapolated. Larger fixed-ratio tests, including n=8,m=18, exceeded the
resource limits. No positive delta has been identified.

The global-swap and capped batch variants still fail on n=4,m=11 and n=5,m=13.
These are failures of the tested policies, not statements about phi(n).

## A diagnosed greedy failure

Replay the global-repair counterexample on n=4,m=11. At turn 8, its chosen
batch leaves next-two-move repair cost 5. Enumerating all 68 full-budget
deletion allocations on that 19-free-edge contracted board finds cost 4 is
possible. Thus the greedy repair has a genuine batch-selection weakness.
The batch variant avoids that particular failure but a different Maker
continuation still defeats it. Local repair alone does not solve planning.

Maker's successful attacks grow one terminal component first, then build
auxiliary components and switch to the other terminal. A cut can look nearly
closed while these mergers create more than n joining edges in one turn.
The next promising development is a potential controlling both terminal
attachment capacities and auxiliary-component threats, with a reserve for
future repairs. It should allow mixed deletions across cuts and optimize whole
batches. Do not assume such a potential exists or infer coefficient 3 here.

## Reproduction and checks

From the repository root:

```
python lower-bound/experiments/verify_moving_cut.py
python lower-bound/experiments/moving_cut.py
```

Both use the standard library; verification imports the existing horizon
solver from the sibling upper-bound experiments directory. Seed 215 is used
only for 120 finite validation boards. Those checks compare symmetry-reduced
cuts with every original partition, validate deletion legality, and compare
the risk score with explicit contractions. They passed. An independent raw
edge-mask check, including internal Maker claims, confirms the global-repair
win at n=2,m=6 (109 raw Maker states).

No Lean targets or trusted definitions were changed. These are Python-checked
finite strategy results and exploratory lessons, not kernel-checked endpoint
theorems. Results under time limits can vary by machine; read printed statuses.
