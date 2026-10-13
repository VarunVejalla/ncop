import NCop.Frontier
import NCop.TwoFrontier
import NCop.StrategyCriterion

namespace NCop

/-- Raw-game invariant corresponding to the two-frontier proof.

This is intentionally a wrapper structure rather than the main game
definition. It records the finite Maker components and the deletion-budget
bookkeeping in the language of the raw game. -/
structure TwoFrontierRaw {m : Nat} (n : Nat) (T : Terminals m) (B : Board m) where
  r : Nat
  source_le_target :
    (B.reachableFinset T.s).card <= (B.reachableFinset T.t).card
  balanced_left :
    (B.reachableFinset T.s).card <= (B.reachableFinset T.t).card + 1
  balanced_right :
    (B.reachableFinset T.t).card <= (B.reachableFinset T.s).card + 1
  sum_sizes :
    (B.reachableFinset T.s).card + (B.reachableFinset T.t).card = r + 2
  breaker_budget : AtMost (r * n) B.breaker
  valid : B.Valid

namespace TwoFrontierRaw

variable {m n : Nat} {T : Terminals m} {B : Board m}

noncomputable def sourceNumericalState (h : TwoFrontierRaw n T B) : TwoFrontierState where
  m := m
  n := n
  r := h.r
  S := (B.reachableFinset T.s).card
  T := (B.reachableFinset T.t).card
  h_sum := h.sum_sizes
  h_bal_left := h.source_le_target
  h_bal_right := by
    exact h.balanced_right

/-- If the source side is the smaller side and the numerical `4n` hypotheses
hold, then after Breaker's next deletion move there is a free edge leaving the
source component.

This is the main bridge from the numerical wrapper into the raw game. -/
theorem exists_free_source_edge_after_breaker
    (h : TwoFrontierRaw n T B) {D : Edge m -> Prop}
    (hD : LegalBreakerMove n B D) (hn : 1 <= n) (hm : m = 4 * n)
    (hr : h.r <= m - 2) :
    ∃ e, e ∈ (B.addBreakerSet D).sourceFrontier T.s ∧
      (B.addBreakerSet D).free e := by
  classical
  have hbudget :
      AtMost ((h.r + 1) * n) (B.addBreakerSet D).breaker := by
    have hnext := Board.atMost_breaker_addBreakerSet h.breaker_budget hD
    have hbudget_eq : h.r * n + n = (h.r + 1) * n := by
      rw [Nat.add_mul, one_mul]
    simpa [hbudget_eq] using hnext
  have hreach :
      (B.addBreakerSet D).reachableFinset T.s = B.reachableFinset T.s := by
    ext v
    simp [Board.mem_reachableFinset, MakerReach.addBreakerSet_iff]
  let hstate := h.sourceNumericalState
  have hgt := hstate.sourceChoices_gt_deletedBudget_four_mul
    (by simpa [hstate, sourceNumericalState] using hn)
    (by simpa [hstate, sourceNumericalState] using hm)
    (by simpa [hstate, sourceNumericalState] using hr)
  have hcard :
      (h.r + 1) * n <
        ((B.addBreakerSet D).reachableFinset T.s).card *
          (m - ((B.addBreakerSet D).reachableFinset T.s).card) := by
    simpa [TwoFrontierState.deletedBudget, TwoFrontierState.sourceChoices,
      hstate, sourceNumericalState, hreach] using hgt
  exact Board.exists_free_sourceFrontier_of_mul_gt_breakerBudget hbudget hcard

end TwoFrontierRaw

end NCop
