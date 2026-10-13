import NCop.FourNArithmetic
import Mathlib.Tactic

namespace NCop

/-- Purely numerical state for the two-frontier strategy.

`S` and `T` are the sizes of Maker's source and target components before
Maker's next move. `r` is the number of Maker moves already made, so the next
move is move `r + 1`; Breaker has moved `r + 1` times. -/
structure TwoFrontierState where
  m : Nat
  n : Nat
  r : Nat
  S : Nat
  T : Nat
  h_sum : S + T = r + 2
  h_bal_left : S <= T
  h_bal_right : T <= S + 1

namespace TwoFrontierState

def deletedBudget (st : TwoFrontierState) : Nat :=
  (st.r + 1) * st.n

def sourceChoices (st : TwoFrontierState) : Nat :=
  st.S * (st.m - st.S)

/-- The smaller frontier has size at least `(r + 1) / 2`, expressed without
division so it is easier to use over naturals. -/
theorem two_mul_S_ge_r_add_one (st : TwoFrontierState) :
    st.r + 1 <= 2 * st.S := by
  have hT : st.T <= st.S + 1 := st.h_bal_right
  have hsum : st.S + st.T = st.r + 2 := st.h_sum
  omega

theorem S_le_half_m_of_sum_le_m (st : TwoFrontierState)
    (hsum_le : st.S + st.T <= st.m) :
    2 * st.S <= st.m := by
  have hST : st.S <= st.T := st.h_bal_left
  omega

/-- If the graph has `4n` vertices and the two-frontier invariant holds before
a nonfinal move, then the crude count `S(m-S)` beats Breaker's total deletion
budget. This is the numeric heart of the `4n` proof. -/
theorem sourceChoices_gt_deletedBudget_four_mul
    (st : TwoFrontierState) (hn : 1 <= st.n) (hm : st.m = 4 * st.n)
    (hr : st.r <= st.m - 2) :
    st.deletedBudget < st.sourceChoices := by
  have hsum_le_m : st.S + st.T <= st.m := by
    rw [st.h_sum]
    omega
  have hS_lower_nat : st.r + 1 <= 2 * st.S :=
    st.two_mul_S_ge_r_add_one
  have hS_upper_nat : 2 * st.S <= st.m :=
    st.S_le_half_m_of_sum_le_m hsum_le_m
  have hquad := four_n_quadratic_margin (n := st.n) (r := st.r) hn (by
    rw [hm] at hr
    exact hr)
  have hS_lower_real : (((st.r + 1 : Nat) : ℝ) / 2) <= (st.S : ℝ) := by
    have hcast : ((st.r + 1 : Nat) : ℝ) <= 2 * (st.S : ℝ) := by
      exact_mod_cast hS_lower_nat
    linarith
  have hS_upper_real : (st.S : ℝ) <= ((st.m : ℝ) / 2) := by
    have hcast : 2 * (st.S : ℝ) <= (st.m : ℝ) := by
      exact_mod_cast hS_upper_nat
    linarith
  have hm_real : (st.m : ℝ) = 4 * (st.n : ℝ) := by exact_mod_cast hm
  have hmono :
      (((st.r + 1 : Nat) : ℝ) / 2) *
          ((st.m : ℝ) - (((st.r + 1 : Nat) : ℝ) / 2))
        <= (st.S : ℝ) * ((st.m : ℝ) - st.S) := by
    -- On `[0, m/2]`, `x * (m - x)` is increasing.
    have hdiff :
        (st.S : ℝ) * ((st.m : ℝ) - st.S) -
          (((st.r + 1 : Nat) : ℝ) / 2) *
            ((st.m : ℝ) - (((st.r + 1 : Nat) : ℝ) / 2))
        =
          ((st.S : ℝ) - (((st.r + 1 : Nat) : ℝ) / 2)) *
            ((st.m : ℝ) - st.S - (((st.r + 1 : Nat) : ℝ) / 2)) := by
      ring
    have hleft : 0 <= (st.S : ℝ) - (((st.r + 1 : Nat) : ℝ) / 2) := by
      linarith
    have hright :
        0 <= (st.m : ℝ) - st.S - (((st.r + 1 : Nat) : ℝ) / 2) := by
      linarith
    nlinarith
  have hreal :
      ((st.deletedBudget : Nat) : ℝ) < ((st.sourceChoices : Nat) : ℝ) := by
    rw [deletedBudget, sourceChoices]
    have hbudget :
        (((st.r + 1 : Nat) : ℝ) * st.n) < (st.S : ℝ) * ((st.m : ℝ) - st.S) := by
      have hquad_m :
          (((st.r + 1 : Nat) : ℝ) / 2) *
            ((st.m : ℝ) - (((st.r + 1 : Nat) : ℝ) / 2)) >
              ((st.r + 1 : Nat) : ℝ) * st.n := by
        simpa [hm] using hquad
      exact lt_of_lt_of_le hquad_m hmono
    have hsub_cast : ((st.m - st.S : Nat) : ℝ) = (st.m : ℝ) - st.S := by
      have hSm : st.S <= st.m := by omega
      exact Nat.cast_sub hSm
    rw [Nat.cast_mul, Nat.cast_mul, hsub_cast]
    exact hbudget
  exact_mod_cast hreal

end TwoFrontierState

end NCop
