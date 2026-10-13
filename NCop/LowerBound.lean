import NCop.BalancedOrientation
import Mathlib.Algebra.Order.Archimedean.Basic

namespace NCop

/-- The explicit partition-matroid certificate proves this finite bound.
The additive slack is immaterial for the asymptotic coefficient. -/
theorem breakerWins_of_add_four_le_two_mul {m n : Nat} (hm : m + 4 ≤ 2 * n) :
    BreakerWins m n := by
  intro T
  have hn : 1 ≤ n := by omega
  have hcolors : (m + 1) / 2 + 2 ≤ n + 1 := by omega
  exact ((balancedSinkOrientation T hcolors).certificate hn).breakerWin

/-- Lower endpoint for the Breaker-first terminal connection game. -/
theorem breakerLowerBound_two : BreakerLowerBound 2 := by
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_ge ((4 : ℝ) / eps)
  refine ⟨N, ?_⟩
  intro n m hn hm
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfour : (4 : ℝ) ≤ eps * (n : ℝ) := by
    have hdiv := (div_le_iff₀ heps).mp (hN.trans hNn)
    nlinarith
  have hfinite : (m : ℝ) + 4 ≤ 2 * (n : ℝ) := by nlinarith
  exact breakerWins_of_add_four_le_two_mul (by exact_mod_cast hfinite)

end NCop
