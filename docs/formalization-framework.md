# Formalization framework

## Layers

1. **Game semantics:** `NCop.Game` defines legal Breaker-first play and inductive
   force-win predicates on the actual complete-graph edge board.
2. **Strategies:** `NCop.InvariantStrategy` turns preserved invariants into
   force-win proofs. Legal Maker claims strictly decrease the finite free-edge
   count, so no infinite-play assumption is needed.
3. **Finite bounds:** the improved upper endpoint proves
   `4 <= n -> (2 + sqrt(3))*n <= m -> MakerWins m n`. The original four-n
   theorem remains available. The lower endpoint proves
   `m+4 <= 2*n -> BreakerWins m n` from explicit partition-matroid certificates.
4. **Asymptotic statements:** `NCop.LookaheadStrategy` converts the improved
   finite bound to `MakerUpperBound (2 + Real.sqrt 3)` with threshold N=4.
   `NCop.Asymptotic` retains the original coefficient-4 adapter.
   For the additive lower slack, `NCop.LowerBound`
   takes `N >= 4/eps` to prove `BreakerLowerBound 2`. Neither changes the
   trusted target definitions.

The targets quantify over every positive epsilon and every sufficiently large
bias, and then over all boards in the indicated linear range. They make no
claim that `phi(n)/n` converges. The repository does not yet define the least
winning board size as a Lean function `phi` or prove the final analytic
`Filter.liminf`/`Filter.limsup` corollaries. Those are a separate packaging
layer requiring threshold existence, incompatibility of the two winning
predicates, and elementary limit bounds. The current endpoint names refer
precisely to the epsilon/eventually predicates in `NCop.Target`.

## Upper proof

`BalancedTrees` stores explicit disjoint terminal trees, balanced sizes,
reachability of every tree vertex, confinement of all claimed edges to those
trees, and the deletion budget. Confinement ensures that any unused vertex is
isolated in Maker's graph. A free edge crossing the smaller tree's cut either
joins the trees or adds exactly one vertex. The cut inequality holds uniformly
for `m >= 4n`. Swapping the trees handles either smaller terminal side.

The earlier complete strategy is `makerWins_of_four_mul_le`, with endpoint
`makerUpperBound_four`. Its growth step now also accepts an arbitrary strict
cut-budget margin and records the incremented expansion count.

The improved strategy counts disjoint deleted cross edges and deleted edges
from each outside vertex. Preventing a two-move threat imposes an additional
per-vertex deletion cost. The finite strategy grows to two components of size
`k = floor((1 + sqrt(3)/3)*n)`. Before that state, the cut inequality guarantees
progress. At that state, the threat count exceeds Breaker's total budget.
Creating more than n immediate winning edges forces a win after any next
legal deletion. A countdown on expansions proves the entire strategy.

The exact arithmetic absorbs rounding: the budget surplus is at least n-3,
so n >= 4 suffices without epsilon slack. The finite theorem is
`makerWins_of_two_add_sqrt_three_mul_le`; the endpoint is
`makerUpperBound_two_add_sqrt_three`, exposed as `Candidate.upper`.
See [the complete argument](../upper-bound/best/lookahead-proof.md).

## Lower proof

The confirmed source is Bednarska--Pikhurko (2005), Theorem 2. The sufficient
independent-cover direction is implemented in `NCop.MatroidStrategy`; the
one-element repair is proved through Mathlib's fundamental-circuit lemmas.
`IndependentCover` keeps `n+1` independent sets covering every available edge
and each containing Maker's set. After a claim, one color needs no repair;
each of the remaining colors needs at most one free edge deleted. The finite
deletion budget and legal-move obligations are proved in the raw game.

`MatroidLowerCertificate` asks for a concrete matroid on the original labeled
edges, a legal opening deletion, an initial cover, and a proof that independence
prevents a terminal path. Providing these certificates for `m <= 2n` immediately
gives `breakerLowerBound_two_of_matroid_certificates`. This conditional theorem
does not itself assert existence of the certificates.

The completed lower proof uses a different concrete certificate:
`NCop.PartitionSafety` pulls back the free matroid on ordinary vertices along
an orientation's tail map. Independent sets have at most one outgoing edge at
each vertex and no outgoing edge at a terminal, so the terminals cannot be
connected. `NCop.BalancedOrientation` constructs a parity tournament and
reserves two extra colors for edges directed into the terminals. Its colors
are injective within each tail fiber, giving an independent cover directly.
`NCop.LowerBound` supplies the certificate and concludes the asymptotic target.

The terminal-identified cycle-matroid construction and its sharper finite
range are now optional alternatives. No paper theorem is imported as an axiom.

## Verification

```sh
lake build NCop Candidates
lake build NCop.ProofAudit
```

Both candidate endpoint theorems are proved. During development, intentional
shared-proof modifications require `python scripts/evaluate_candidate.py
--allow-trusted-dirty`; after committing them, use the default evaluator.

The endpoint axiom audit includes `breakerLowerBound_two`, the original
`makerUpperBound_four`, and `makerUpperBound_two_add_sqrt_three`, as well as
their finite strategy theorems. Permitted
dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

Earlier baseline verification on 2026-10-12: `lake build NCop Candidates NCop.ProofAudit`
completed successfully (3315 jobs). Both endpoint audits reported only the
three standard dependencies above. The candidate evaluator with
`--allow-trusted-dirty` accepted `C1 = 2`, `C2 = 4`, and gap `2`.
`git diff --check` passed, and all local Markdown links in the research
documentation resolved. The trusted game and target definitions were unchanged.

Lookahead verification on 2026-10-12: the same full build completed
successfully (3319 jobs), including `Candidate.upper` with coefficient
`2 + Real.sqrt 3`. The disjoint budget lemma, many-winning-edges lemma,
integer-parameter strategy, finite square-root theorem, and asymptotic
endpoint all audited to only `propext`, `Classical.choice`, and `Quot.sound`.
The trusted `Game.lean` and `Target.lean` definitions remain unchanged.
The candidate evaluator with `--allow-trusted-dirty` accepted coefficients
2 and `2 + Real.sqrt 3`, with gap `1.7320508075688772`. Local Markdown
links resolved and `git diff --check` passed.
