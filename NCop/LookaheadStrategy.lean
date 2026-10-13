import NCop.LookaheadThreat
import NCop.LookaheadArithmetic

namespace NCop

/-- Complete finite strategy, parametrized by an integer stopping size.
Breaker moves first. Every intervening growth and final threat is certified. -/
theorem makerWins_of_lookahead_parameters {m n k : Nat}
    (hk : 1 ≤ k) (hnk : n ≤ k) (hkn : k ≤ 2*n)
    (hspace : k+2*n < m)
    (hmargin : (2*k-1)*n < k*k+(m-2*k)*(2*(k-n))) : MakerWins m n := by
  classical
  intro T
  have hfrom : ∀ fuel : Nat, ∀ (B : Board m) (h : BalancedTrees n T B),
      h.r + fuel = 2*k-2 → MakerWinFrom T n B := by
    intro fuel
    induction fuel with
    | zero =>
      intro B h hr
      have hs := h.sum_sizes
      have hbA := h.balancedA
      have hbC := h.balancedC
      have ha : h.A.card = k := by omega
      have hc : h.C.card = k := by omega
      by_cases hp : MakerHasPath T B
      · exact .doneBefore hp
      apply MakerCanForce.surviveDelete h.valid hp
      intro D hD
      exact lookahead_win_at_equal h ha hc hnk hkn hmargin hD
    | succ fuel ih =>
      intro B h hr
      by_cases hp : MakerHasPath T B
      · exact .doneBefore hp
      apply MakerCanForce.surviveDelete h.valid hp
      intro D hD
      by_cases hpD : MakerHasPath T (B.addBreakerSet D)
      · exact .doneAfter hpD
      have hcut : ∀ {U : Terminals m} (g : BalancedTrees n U B),
          g.r = h.r → g.A.card ≤ g.C.card →
          (g.r+1)*n < g.A.card*(m-g.A.card) := by
        intro U g hgr hsmall
        have hsum := g.sum_sizes
        have hbal := g.balancedC
        have hapos : 0 < g.A.card := by omega
        have hsize : g.A.card ≤ k := by omega
        have hrle : g.r+1 ≤ 2*g.A.card := by omega
        have hroom : 2*n < m-g.A.card := by omega
        have hmul := Nat.mul_lt_mul_of_pos_left hroom hapos
        have hbudget := Nat.mul_le_mul_right n hrle
        nlinarith
      by_cases hsmall : h.A.card ≤ h.C.card
      · obtain ⟨e,he,hnext⟩ := h.grow_of_margin (hcut h rfl hsmall) hsmall hD
        apply MakerCanForce.claim (Board.valid_after_legal_breaker hD) hpD he
        rcases hnext with hw | ⟨hnew,hnewr⟩
        · exact .doneBefore hw
        · exact ih _ hnew (by omega)
      · have hsmall' : h.swap.A.card ≤ h.swap.C.card := Nat.le_of_lt (lt_of_not_ge hsmall)
        obtain ⟨e,he,hnext⟩ := h.swap.grow_of_margin
          (hcut h.swap rfl hsmall') hsmall' hD
        apply MakerCanForce.claim (Board.valid_after_legal_breaker hD) hpD he
        rcases hnext with hw | ⟨hnew,hnewr⟩
        · exact .doneBefore (makerHasPath_swap_iff.mp hw)
        · have hnewr' : hnew.r = h.r+1 := hnewr
          apply ih _ hnew.swap
          change hnew.r + fuel = 2*k-2
          omega
  exact hfrom (2*k-2) (Board.empty m) (BalancedTrees.initial T) (by simp [BalancedTrees.initial])

/-- Finite two-move lookahead bound, with Breaker first. -/
theorem makerWins_of_two_add_sqrt_three_mul_le {m n : Nat} (hn : 4 ≤ n)
    (hm : (2+Real.sqrt 3)*(n:ℝ) ≤ m) : MakerWins m n := by
  obtain ⟨k,hk,hnk,hkn,hspace,_,hmargin⟩ := lookahead_parameters hn hm
  exact makerWins_of_lookahead_parameters hk hnk hkn hspace hmargin

theorem makerUpperBound_two_add_sqrt_three : MakerUpperBound (2+Real.sqrt 3) := by
  intro eps heps
  refine ⟨4, ?_⟩
  intro n m hn hm
  apply makerWins_of_two_add_sqrt_three_mul_le hn
  have hnonneg : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end NCop
