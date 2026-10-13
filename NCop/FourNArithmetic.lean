import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NCop

/-- Real-valued core of the `4n` quadratic inequality. -/
theorem four_n_quadratic_margin_real {a N : ℝ} (ha : 0 < a) (haN : a < 4 * N) :
    (a / 2) * (4 * N - a / 2) > a * N := by
  have hdiff : (a / 2) * (4 * N - a / 2) - a * N = a * (4 * N - a) / 4 := by
    ring
  have hpos : 0 < a * (4 * N - a) / 4 := by
    have hN : 0 < 4 * N - a := by linarith
    exact div_pos (mul_pos ha hN) (by norm_num)
  linarith

/-- The elementary inequality behind the two-frontier `4n` upper-bound proof.

Before robber move `r + 1`, the smaller frontier has size at least
`(r + 1) / 2`. If `m = 4n` and `r ≤ 4n - 2`, then even the lower bound
`((r + 1) / 2) * (4n - (r + 1) / 2)` beats the total deletion budget
`(r + 1)n`.
-/
theorem four_n_quadratic_margin {n r : Nat} (hn : 1 <= n)
    (hr : r <= 4 * n - 2) :
    (((r + 1 : Nat) : ℝ) / 2) *
      ((4 * n : Nat) - (((r + 1 : Nat) : ℝ) / 2)) >
        ((r + 1 : Nat) : ℝ) * n := by
  have hcast : ((4 * n : Nat) : ℝ) = 4 * (n : ℝ) := by norm_num
  rw [hcast]
  apply four_n_quadratic_margin_real
  · positivity
  · have hcalc : (r + 1 : Nat) < 4 * n := by omega
    exact_mod_cast hcalc

end NCop
