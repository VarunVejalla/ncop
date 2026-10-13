import NCop.MatroidRepair
import NCop.InvariantStrategy
import NCop.Lemmas
import NCop.Asymptotic

namespace NCop

/-- Independent sets cover free edges and all contain Maker's claimed set.
Deleted edges belong to none of the covering sets. -/
structure IndependentCover {m : Nat} (M : Matroid (Edge m)) (k : Nat) (B : Board m) where
  sets : Fin k → Set (Edge m)
  indep : ∀ i, M.Indep (sets i)
  common : ∀ i e, B.maker e → e ∈ sets i
  covered : ∀ e, B.free e → ∃ i, e ∈ sets i
  undeleted : ∀ i e, e ∈ sets i → ¬ B.breaker e

namespace IndependentCover

theorem maker_indep {m n : Nat} {M : Matroid (Edge m)} {B : Board m}
    (h : IndependentCover M (n + 1) B) : M.Indep {e | B.maker e} :=
  (h.indep 0).subset (h.common 0)

/-- The sufficient direction of Bednarska--Pikhurko's biased circuit theorem:
after a claim, at most `n` free deletions restore a cover by `n+1` independent
sets. The already safe color is excluded from the repair budget. -/
theorem repair {m n : Nat} {M : Matroid (Edge m)} {B : Board m}
    (h : IndependentCover M (n + 1) B) {e : Edge m}
    (he : LegalMakerMove B e) :
    M.Indep {f | (B.addMaker e).maker f} ∧
      ∃ D, LegalBreakerMove n (B.addMaker e) D ∧
        Nonempty (IndependentCover M (n + 1) ((B.addMaker e).addBreakerSet D)) := by
  classical
  obtain ⟨j, hej⟩ := h.covered e he.2
  have hprotected : M.Indep (insert e {f | B.maker f}) := by
    apply (h.indep j).subset
    intro f hf
    rcases hf with rfl | hf
    · exact hej
    · exact h.common j f hf
  have hnewMaker : M.Indep {f | (B.addMaker e).maker f} := by
    convert hprotected using 1
    ext f
    simp [Board.addMaker, Set.mem_insert_iff, or_comm]
  refine ⟨hnewMaker, ?_⟩
  let needs : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i => ¬ M.Indep (insert e (h.sets i))
  have hj : j ∉ needs := by
    simp [needs, Set.insert_eq_of_mem hej, h.indep j]
  have hcount : needs.card ≤ n := by
    have hs : needs ⊆ Finset.univ.erase j := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨fun hij => hj (hij ▸ hi), Finset.mem_univ i⟩
    simpa using Finset.card_le_card hs
  have hrepair : ∀ i : {i // i ∈ needs},
      ∃ x, (B.addMaker e).free x ∧ M.Indep (insert e (h.sets i.val) \ {x}) := by
    intro i
    have hnot : ¬ M.Indep (insert e (h.sets i.val)) :=
      (Finset.mem_filter.mp i.property).2
    rcases matroid_exists_repair_outside_protected (h.indep i.val) hprotected
      ((h.indep j).subset_ground hej) with hs | ⟨x, hxI, hxP, hxe, hxind⟩
    · exact False.elim (hnot hs)
    · refine ⟨x, ⟨?_, h.undeleted i.val x hxI⟩, hxind⟩
      intro hx
      rcases hx with hx | hxe'
      · exact hxP hx
      · exact hxe hxe'
  let chosen : {i // i ∈ needs} → Edge m := fun i => Classical.choose (hrepair i)
  have hchosen : ∀ i, (B.addMaker e).free (chosen i) ∧
      M.Indep (insert e (h.sets i.val) \ {chosen i}) :=
    fun i => Classical.choose_spec (hrepair i)
  let deleted : Finset (Edge m) := needs.attach.image chosen
  let D : Edge m → Prop := fun f => f ∈ deleted
  have hDfree : ∀ f, D f → (B.addMaker e).free f := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact (hchosen i).1
  have hD : LegalBreakerMove n (B.addMaker e) D := by
    refine ⟨valid_addMaker he, hDfree, ?_⟩
    apply atMost_of_finset_support D deleted (fun _ hf => hf)
    exact (Finset.card_image_le.trans (by simpa using hcount))
  refine ⟨D, hD, ⟨{
    sets := fun i => insert e (h.sets i) \ (deleted : Set (Edge m))
    indep := ?_
    common := ?_
    covered := ?_
    undeleted := ?_
  }⟩⟩
  · intro i
    by_cases hi : i ∈ needs
    · let idx : {i // i ∈ needs} := ⟨i, hi⟩
      apply (hchosen idx).2.subset
      intro f hf
      refine ⟨hf.1, ?_⟩
      intro hfx
      have hxdel : chosen idx ∈ deleted :=
        Finset.mem_image.mpr ⟨idx, Finset.mem_attach _ _, rfl⟩
      exact hf.2 (Set.mem_singleton_iff.mp hfx ▸ hxdel)
    · have hind : M.Indep (insert e (h.sets i)) := by
        by_contra hnot
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot⟩)
      exact hind.subset Set.diff_subset
  · intro i f hf
    refine ⟨?_, ?_⟩
    · rcases hf with hf | rfl
      · exact Set.mem_insert_of_mem e (h.common i f hf)
      · exact Set.mem_insert f _
    · intro hdel
      exact (hDfree f hdel).1 hf
  · intro f hf
    have hfB : B.free f :=
      ⟨fun hmaker => hf.1 (Or.inl hmaker), fun hbreaker => hf.2 (Or.inl hbreaker)⟩
    obtain ⟨i, hi⟩ := h.covered f hfB
    exact ⟨i, Set.mem_insert_of_mem e hi, fun hdel => hf.2 (Or.inr hdel)⟩
  · intro i f hf hbreaker
    rcases hbreaker with hbreaker | hdel
    · rcases hf.1 with rfl | hfI
      · exact he.2.2 hbreaker
      · exact h.undeleted i f hfI hbreaker
    · exact hf.2 hdel

end IndependentCover

/-- A safe matroid cover gives an actual Breaker win in the raw terminal
game, before Maker's turn. The graph-to-matroid reduction enters only through
`hsafe`, which must be proved for the chosen matroid. -/
theorem breakerWinAfter_of_independentCover {m n : Nat}
    (T : Terminals m) (M : Matroid (Edge m))
    (hsafe : ∀ B : Board m, M.Indep {e | B.maker e} → ¬ MakerHasPath T B) :
    ∀ B : Board m, B.Valid → Nonempty (IndependentCover M (n + 1) B) →
      BreakerWinAfter T n B := by
  intro B
  refine (invImage Board.freeCount Nat.lt_wfRel).wf.induction
    (C := fun B => B.Valid → Nonempty (IndependentCover M (n + 1) B) →
      BreakerWinAfter T n B) B ?_
  intro B ih hv hcover
  obtain ⟨h⟩ := hcover
  refine BreakerCanForce.reply hv (hsafe B h.maker_indep) ?_
  intro e he
  obtain ⟨hind, D, hD, hcover'⟩ := h.repair he
  refine BreakerCanForce.delete (valid_addMaker he) (hsafe _ hind) hD ?_
  have hDold : LegalBreakerMove n B D := by
    refine ⟨hv, ?_, hD.2.2⟩
    intro f hf
    have hfree := hD.2.1 f hf
    exact ⟨fun hfmaker => hfree.1 (Or.inl hfmaker), hfree.2⟩
  have heD : LegalMakerMove (B.addBreakerSet D) e := by
    refine ⟨Board.valid_after_legal_breaker hDold, he.2.1, ?_⟩
    intro hdel
    rcases hdel with hdel | hdel
    · exact he.2.2 hdel
    · exact (hD.2.1 e hdel).1 (Or.inr rfl)
  exact ih _ (Board.freeCount_claim_after_delete_lt heD)
    (Board.valid_after_legal_breaker hD) hcover'

/-- Concrete obligations for applying the matroid strategy to an initial
terminal board: a legal opening deletion, an independent cover of the
remaining board, and the implication from independence to terminal safety. -/
structure MatroidLowerCertificate {m : Nat} (n : Nat) (T : Terminals m) where
  matroid : Matroid (Edge m)
  opening : Edge m → Prop
  legal : LegalBreakerMove n (Board.empty m) opening
  cover : Nonempty (IndependentCover matroid (n + 1)
    ((Board.empty m).addBreakerSet opening))
  safe : ∀ B : Board m, matroid.Indep {e | B.maker e} → ¬ MakerHasPath T B

theorem MatroidLowerCertificate.breakerWin {m n : Nat} {T : Terminals m}
    (h : MatroidLowerCertificate n T) : BreakerWinFrom T n (Board.empty m) := by
  refine BreakerCanForce.delete (empty_valid m) ?_ h.legal ?_
  · exact not_makerHasPath_of_avoids_source (empty_makerAvoidsVertex T.s)
  · exact breakerWinAfter_of_independentCover T h.matroid h.safe _
      (Board.valid_after_legal_breaker h.legal) h.cover

/-- Producing the concrete certificates for `m <= 2n` finishes the lower
endpoint. This is a conditional conversion theorem, not the missing bound. -/
theorem breakerLowerBound_two_of_matroid_certificates
    (h : ∀ n m : Nat, 1 ≤ n → m ≤ 2 * n →
      ∀ T : Terminals m, Nonempty (MatroidLowerCertificate n T)) :
    BreakerLowerBound 2 := by
  apply breakerLowerBound_of_linear_wins 2
  intro n m hn hm T
  obtain ⟨cert⟩ := h n m hn hm T
  exact cert.breakerWin

end NCop
