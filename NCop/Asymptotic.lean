import NCop.Target
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace NCop

/-- A uniform finite linear winning bound implies the asymptotic Maker target.
The threshold excludes zero bias, where the game has different edge cases. -/
theorem makerUpperBound_of_linear_wins (c : Nat)
    (h : ∀ n m : Nat, 1 ≤ n → c * n ≤ m → MakerWins m n) :
    MakerUpperBound (c : ℝ) := by
  intro eps heps
  refine ⟨1, ?_⟩
  intro n m hn hm
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (c : ℝ) * (n : ℝ) ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right (by linarith : (c : ℝ) ≤ c + eps) hnreal).trans hm
  exact h n m hn (by exact_mod_cast hcn)

/-- A uniform finite linear Breaker bound implies the asymptotic lower target. -/
theorem breakerLowerBound_of_linear_wins (c : Nat)
    (h : ∀ n m : Nat, 1 ≤ n → m ≤ c * n → BreakerWins m n) :
    BreakerLowerBound (c : ℝ) := by
  intro eps heps
  refine ⟨1, ?_⟩
  intro n m hn hm
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmc : (m : ℝ) ≤ (c : ℝ) * (n : ℝ) :=
    hm.trans (mul_le_mul_of_nonneg_right (by linarith : (c : ℝ) - eps ≤ c) hnreal)
  exact h n m hn (by exact_mod_cast hmc)

end NCop
