import Mathlib.Data.Real.Basic
import NCop.Game

namespace NCop

/-- Asymptotic lower bound on `phi(n)`: for every positive epsilon and all
sufficiently large `n`, Breaker wins whenever `m <= (c - epsilon) n`. -/
def BreakerLowerBound (c : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps ->
    ∃ N : Nat, ∀ n m : Nat,
      N <= n ->
      (m : ℝ) <= (c - eps) * (n : ℝ) ->
      BreakerWins m n

/-- Asymptotic upper bound on `phi(n)`: for every positive epsilon and all
sufficiently large `n`, Maker wins whenever `(c + epsilon) n <= m`. -/
def MakerUpperBound (c : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps ->
    ∃ N : Nat, ∀ n m : Nat,
      N <= n ->
      (c + eps) * (n : ℝ) <= (m : ℝ) ->
      MakerWins m n

end NCop
