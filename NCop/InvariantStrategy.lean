import NCop.Counting

namespace NCop

namespace Board

theorem valid_after_legal_breaker {m n : Nat} {B : Board m}
    {D : Edge m → Prop} (hD : LegalBreakerMove n B D) :
    (B.addBreakerSet D).Valid := by
  intro e he
  rcases he.2 with hB | hdel
  · exact hD.1 e ⟨he.1, hB⟩
  · exact (hD.2.1 e hdel).1 he.1

/-- Every legal claim consumes a free edge, even when preceded by deletions.
This supplies termination for both invariant-based strategy constructions. -/
theorem freeCount_claim_after_delete_lt {m : Nat} {B : Board m}
    {D : Edge m → Prop} {e : Edge m}
    (he : LegalMakerMove (B.addBreakerSet D) e) :
    ((B.addBreakerSet D).addMaker e).freeCount < B.freeCount := by
  classical
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [mem_freeFinset] at hf ⊢
    exact ⟨fun h => hf.1 (Or.inl h), fun h => hf.2 (Or.inl h)⟩
  · intro hsub
    have heB : e ∈ B.freeFinset := by
      rw [mem_freeFinset]
      exact ⟨he.2.1, fun h => he.2.2 (Or.inl h)⟩
    have heNew := hsub heB
    rw [mem_freeFinset] at heNew
    exact heNew.1 (Or.inr rfl)

end Board

/-- A Maker invariant needs only a legal claim that wins immediately or
restores the invariant after every legal Breaker move. Free-edge count gives
the well-founded rank automatically. -/
theorem makerWinFrom_of_invariant {m n : Nat} (T : Terminals m)
    (Inv : Board m → Prop)
    (hvalid : ∀ B, Inv B → B.Valid)
    (hstep : ∀ B, Inv B → ¬ MakerHasPath T B →
      ∀ D, LegalBreakerMove n B D →
        ∃ e, LegalMakerMove (B.addBreakerSet D) e ∧
          (MakerHasPath T ((B.addBreakerSet D).addMaker e) ∨
            Inv ((B.addBreakerSet D).addMaker e))) :
    ∀ B, Inv B → MakerWinFrom T n B := by
  intro B
  refine (invImage Board.freeCount Nat.lt_wfRel).wf.induction
    (C := fun B => Inv B → MakerWinFrom T n B) B ?_
  intro B ih hInv
  by_cases hp : MakerHasPath T B
  · exact MakerCanForce.doneBefore hp
  · refine MakerCanForce.surviveDelete (hvalid B hInv) hp ?_
    intro D hD
    by_cases hpD : MakerHasPath T (B.addBreakerSet D)
    · exact MakerCanForce.doneAfter hpD
    · obtain ⟨e, he, hnext⟩ := hstep B hInv hp D hD
      refine MakerCanForce.claim (Board.valid_after_legal_breaker hD) hpD he ?_
      rcases hnext with hwin | hInv'
      · exact MakerCanForce.doneBefore hwin
      · exact ih _ (Board.freeCount_claim_after_delete_lt he) hInv'

/-- A Breaker invariant is safe now, and can be made safe after a deletion
and restored after every legal Maker reply. Finite edge consumption turns
this safety strategy into the inductive force-win predicate. -/
theorem breakerWinFrom_of_invariant {m n : Nat} (T : Terminals m)
    (Inv : Board m → Prop)
    (hvalid : ∀ B, Inv B → B.Valid)
    (hsafe : ∀ B, Inv B → ¬ MakerHasPath T B)
    (hstep : ∀ B, Inv B → ¬ B.noFreeEdges →
      ∃ D, LegalBreakerMove n B D ∧
        ¬ MakerHasPath T (B.addBreakerSet D) ∧
        ∀ e, LegalMakerMove (B.addBreakerSet D) e →
          Inv ((B.addBreakerSet D).addMaker e)) :
    ∀ B, Inv B → BreakerWinFrom T n B := by
  intro B
  refine (invImage Board.freeCount Nat.lt_wfRel).wf.induction
    (C := fun B => Inv B → BreakerWinFrom T n B) B ?_
  intro B ih hInv
  by_cases hend : B.noFreeEdges
  · exact BreakerCanForce.doneBefore (hvalid B hInv) (hsafe B hInv) hend
  · obtain ⟨D, hD, hsafeD, hreply⟩ := hstep B hInv hend
    refine BreakerCanForce.delete (hvalid B hInv) (hsafe B hInv) hD ?_
    refine BreakerCanForce.reply (Board.valid_after_legal_breaker hD) hsafeD ?_
    intro e he
    exact ih _ (Board.freeCount_claim_after_delete_lt he) (hreply e he)

end NCop
