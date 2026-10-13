import NCop.LookaheadCounting

namespace NCop

theorem makerCanForce_swap {m n : Nat} {T : Terminals m} {B : Board m}
    {turn : MakerTurn} (h : MakerCanForce T.swap n turn B) :
    MakerCanForce T n turn B := by
  induction h with
  | doneBefore hp => exact .doneBefore (makerHasPath_swap_iff.mp hp)
  | doneAfter hp => exact .doneAfter (makerHasPath_swap_iff.mp hp)
  | surviveDelete hv hp _ ih =>
    exact .surviveDelete hv (fun hp' => hp (makerHasPath_swap_iff.mpr hp')) ih
  | claim hv hp he _ ih =>
    exact .claim hv (fun hp' => hp (makerHasPath_swap_iff.mpr hp')) he ih

/-- More than n free edges, each winning on claim, survive the next deletion. -/
theorem makerWinFrom_of_many_winning_edges {m n : Nat} {T : Terminals m}
    {B : Board m} (hv : B.Valid) (E : Finset (Edge m)) (hn : n < E.card)
    (hfree : ∀ e ∈ E, B.free e)
    (hwin : ∀ e ∈ E, MakerHasPath T (B.addMaker e)) : MakerWinFrom T n B := by
  classical
  by_cases hp : MakerHasPath T B
  · exact .doneBefore hp
  apply MakerCanForce.surviveDelete hv hp
  intro D hD
  by_cases hpD : MakerHasPath T (B.addBreakerSet D)
  · exact .doneAfter hpD
  have hcard : (E.filter D).card ≤ n :=
    finset_card_le_of_atMost hD.2.2 _ (fun _ he => (Finset.mem_filter.mp he).2)
  have hex : ∃ e ∈ E, ¬ D e := by
    by_contra h
    have hall : E.filter D = E := by
      apply Finset.filter_eq_self.mpr
      intro e he
      by_contra hde
      exact h ⟨e,he,hde⟩
    rw [hall] at hcard
    omega
  obtain ⟨e,he,hde⟩ := hex
  have hlegal : LegalMakerMove (B.addBreakerSet D) e :=
    ⟨Board.valid_after_legal_breaker hD, (hfree e he).1,
      fun hb => hb.elim (hfree e he).2 hde⟩
  refine .claim (Board.valid_after_legal_breaker hD) hpD hlegal (.doneBefore ?_)
  exact MakerReach.addBreakerSet_iff.mpr (hwin e he)

namespace BalancedTrees

theorem join_path {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) {D : Edge m → Prop} {e : Edge m}
    (he : e ∈ Edge.betweenSets h.A h.C) :
    MakerHasPath T ((B.addBreakerSet D).addMaker e) := by
  obtain ⟨u,hu,v,hv,hi⟩ := Edge.mem_betweenSets.mp he
  have ha : MakerReach ((B.addBreakerSet D).addMaker e) T.s u :=
    (MakerReach.addBreakerSet_iff.mpr (h.connectedA u hu)).claim_mono
  have hc : MakerReach ((B.addBreakerSet D).addMaker e) T.t v :=
    (MakerReach.addBreakerSet_iff.mpr (h.connectedC v hv)).claim_mono
  exact ha.trans ((MakerReach.of_adjacent ⟨e,Or.inr rfl,hi⟩).trans hc.reverse)

/-- A free attachment and > n edges into the other tree force a two-move win. -/
theorem attachment_win {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) {D : Edge m → Prop}
    (hD : LegalBreakerMove n B D) {v : Fin m} (_hv : v ∉ h.A ∪ h.C)
    (hattach : 0 < ((B.addBreakerSet D).freeTo h.A v).card)
    (hthreat : n < ((B.addBreakerSet D).freeTo h.C v).card) :
    MakerWinAfter T n (B.addBreakerSet D) := by
  classical
  let Q := B.addBreakerSet D
  obtain ⟨e,he⟩ := Finset.card_pos.mp hattach
  obtain ⟨heA,hefree⟩ := Finset.mem_filter.mp he
  obtain ⟨w,hw,u,hu,hi⟩ := Edge.mem_betweenSets.mp heA
  have hw : w=v := Finset.mem_singleton.mp hw
  subst w
  have hlegal : LegalMakerMove Q e := ⟨Board.valid_after_legal_breaker hD,hefree⟩
  by_cases hp : MakerHasPath T Q
  · exact .doneAfter hp
  apply MakerCanForce.claim (Board.valid_after_legal_breaker hD) hp hlegal
  apply makerWinFrom_of_many_winning_edges (valid_addMaker hlegal)
    (Q.freeTo h.C v) hthreat
  · intro f hf
    obtain ⟨hfC,hffree⟩ := Finset.mem_filter.mp hf
    obtain ⟨w,hw,z,hz,hj⟩ := Edge.mem_betweenSets.mp hfC
    have hw : w=v := Finset.mem_singleton.mp hw
    subst w
    have hfe : f ≠ e := by
      intro hfe
      subst f
      rcases Edge.incident_pairs hi hj with hs | hs
      · exact Finset.disjoint_left.mp h.disjoint hu (hs.2 ▸ hz)
      · exact hi.2.2 hs.2.symm
    exact ⟨fun hm => hm.elim hffree.1 hfe, hffree.2⟩
  · intro f hf
    obtain ⟨hfC,_⟩ := Finset.mem_filter.mp hf
    obtain ⟨w,hw,z,hz,hj⟩ := Edge.mem_betweenSets.mp hfC
    have hw : w=v := Finset.mem_singleton.mp hw
    subst w
    have hA : MakerReach (Q.addMaker e) T.s v :=
      ((MakerReach.addBreakerSet_iff.mpr (h.connectedA u hu)).claim_mono).trans
        (.of_adjacent ⟨e,Or.inr rfl,hi.2.1,hi.1,hi.2.2.symm⟩)
    have hC : MakerReach ((Q.addMaker e).addMaker f) T.t z :=
      ((MakerReach.addBreakerSet_iff.mpr (h.connectedC z hz)).claim_mono).claim_mono
    exact hA.claim_mono.trans
      ((MakerReach.of_adjacent ⟨f,Or.inr rfl,hj⟩).trans hC.reverse)

end BalancedTrees

/-- At the stopping size, budget forces a joining edge or a two-move threat. -/
theorem lookahead_win_at_equal {m n k : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) (ha : h.A.card = k) (hc : h.C.card = k)
    (hnk : n ≤ k) (hkn : k ≤ 2*n)
    (hmargin : (2*k-1)*n < k*k+(m-2*k)*(2*(k-n)))
    {D : Edge m → Prop} (hD : LegalBreakerMove n B D) :
    MakerWinAfter T n (B.addBreakerSet D) := by
  classical
  let Q := B.addBreakerSet D
  have hv : Q.Valid := Board.valid_after_legal_breaker hD
  by_cases hp : MakerHasPath T Q
  · exact .doneAfter hp
  by_cases hj : ∃ e ∈ Edge.betweenSets h.A h.C, Q.free e
  · obtain ⟨e,he,hfree⟩ := hj
    exact .claim hv hp ⟨hv,hfree⟩ (.doneBefore (h.join_path he))
  by_cases hs : ∀ v, v ∉ h.A ∪ h.C →
      ((Q.freeTo h.A v).card = 0 ∨ (Q.freeTo h.C v).card ≤ n) ∧
      ((Q.freeTo h.C v).card = 0 ∨ (Q.freeTo h.A v).card ≤ n)
  · have hb : AtMost ((2*k-1)*n) Q.breaker := by
      have hr := h.sum_sizes
      rw [ha,hc] at hr
      have heq : h.r+1 = 2*k-1 := by omega
      have hb : AtMost ((h.r+1)*n) Q.breaker := by
        simpa [Q,Nat.add_mul] using Board.atMost_breaker_addBreakerSet h.budget hD
      rw [heq] at hb
      exact hb
    have hcount := lookahead_budget h.disjoint ha hc hnk hkn hb
      (fun e he => by
        by_contra hbr
        exact hj ⟨e,he,h.not_maker_cross he,hbr⟩)
      (fun v hv e he => h.not_maker_outside hv he) hs
    omega
  · obtain ⟨v,hv⟩ := not_forall.mp hs
    obtain ⟨hv,hbad⟩ := Classical.not_imp.mp hv
    by_cases hfirst : (Q.freeTo h.A v).card = 0 ∨ (Q.freeTo h.C v).card ≤ n
    · have hsecond : ¬ ((Q.freeTo h.C v).card = 0 ∨ (Q.freeTo h.A v).card ≤ n) :=
        fun hsecond => hbad ⟨hfirst,hsecond⟩
      push Not at hsecond
      apply makerCanForce_swap
      apply h.swap.attachment_win hD
      · simpa [BalancedTrees.swap,Finset.union_comm] using hv
      · exact Nat.pos_of_ne_zero hsecond.1
      · exact hsecond.2
    · push Not at hfirst
      exact h.attachment_win hD hv (Nat.pos_of_ne_zero hfirst.1) hfirst.2

end NCop
