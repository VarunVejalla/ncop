# Shared research

Contract Maker's claimed components. The weight `E(A,B)` is the number of free
edges between two components. Breaker decreases total edge weight by at most
`n`; Maker selects a positive-weight pair and contracts it. Weights to other
components add. The initial state has singleton components and every weight 1.

Maker wants to merge the two terminal components. Internal component edges do
not help this objective. This model supports strategy analysis, small-state
recurrences, and experiments, but heuristic simulations do not decide the
adversarial game.

Shared methods include potential functions, matroids, LP relaxations,
resistance/conductance, and counting overlaps of possible winning paths.
Whether `phi(n)/n` converges is a separate research question; current bounds
use liminf and limsup without requiring convergence.
