import NCop.Lemmas

namespace NCop

/-- A general Maker strategy criterion.

To prove Maker can force a win from any board satisfying `Inv`, it suffices to
provide a natural-valued rank and show that after every legal Breaker move,
either Maker has already connected the terminals or Maker has a legal claim
that restores `Inv` and strictly decreases the rank.

This is the proof-friendly bridge from invariant/counting arguments to the
inductive game definition `MakerCanForce`.
-/
theorem makerWinFrom_of_decreasing_strategy {m n : Nat} (T : Terminals m)
    (Inv : Board m -> Prop) (rank : Board m -> Nat)
    (hvalid : ∀ B, Inv B -> B.Valid)
    (hstep :
      ∀ B, Inv B -> ¬ MakerHasPath T B ->
        ∀ D, LegalBreakerMove n B D ->
          MakerHasPath T (B.addBreakerSet D) ∨
          ∃ e, LegalMakerMove (B.addBreakerSet D) e ∧
            Inv ((B.addBreakerSet D).addMaker e) ∧
            rank ((B.addBreakerSet D).addMaker e) < rank B) :
    ∀ B, Inv B -> MakerWinFrom T n B := by
  intro B
  refine (invImage rank Nat.lt_wfRel).wf.induction
    (C := fun B => Inv B -> MakerWinFrom T n B) B ?_
  intro B ih hInv
  by_cases hpath : MakerHasPath T B
  · exact MakerCanForce.doneBefore hpath
  · refine MakerCanForce.surviveDelete (hvalid B hInv) hpath ?_
    intro D hD
    let BD := B.addBreakerSet D
    by_cases hpathD : MakerHasPath T BD
    · exact MakerCanForce.doneAfter hpathD
    · rcases hstep B hInv hpath D hD with hdone | ⟨e, hlegal, hInv', hrank⟩
      · exact False.elim (hpathD hdone)
      · exact MakerCanForce.claim (valid_addBreakerSet hD) hpathD hlegal
          (ih ((B.addBreakerSet D).addMaker e) hrank hInv')

end NCop
