import NCop.Game
import NCop.Counting

namespace NCop

namespace Board

variable {m : Nat}

/-- Maker has not claimed any edge touching `v`. -/
def makerAvoidsVertex (B : Board m) (v : Fin m) : Prop :=
  ∀ e, B.maker e -> ¬ Edge.touches e v

end Board

/-- If Maker has claimed no edge touching `s`, then Maker cannot reach any
different vertex from `s`. -/
theorem not_makerReach_of_avoids_left {m : Nat} {B : Board m} {s t : Fin m}
    (havoid : B.makerAvoidsVertex s) (hst : s ≠ t) :
    ¬ MakerReach B s t := by
  intro hreach
  cases hreach with
  | refl v =>
      exact hst rfl
  | step adj _ =>
      rcases adj with ⟨e, hmaker, hincident⟩
      exact havoid e hmaker hincident.1

/-- Source-isolation form of the previous lemma, packaged for terminals. -/
theorem not_makerHasPath_of_avoids_source {m : Nat} {T : Terminals m}
    {B : Board m} (havoid : B.makerAvoidsVertex T.s) :
    ¬ MakerHasPath T B := by
  exact not_makerReach_of_avoids_left havoid T.distinct

@[simp] theorem empty_valid (m : Nat) : (Board.empty m).Valid := by
  intro e h
  exact h.1

@[simp] theorem empty_makerAvoidsVertex {m : Nat} (v : Fin m) :
    (Board.empty m).makerAvoidsVertex v := by
  intro e hmaker
  cases hmaker

theorem valid_addBreakerSet {m : Nat} {B : Board m} {D : Edge m -> Prop}
    (hlegal : LegalBreakerMove n B D) : (B.addBreakerSet D).Valid := by
  intro e h
  rcases h with ⟨hmaker, hbreaker⟩
  rcases hlegal with ⟨hvalid, hfree, _⟩
  rcases hbreaker with hbreaker | hD
  · exact hvalid e ⟨hmaker, hbreaker⟩
  · exact (hfree e hD).1 hmaker

theorem valid_addMaker {m : Nat} {B : Board m} {e0 : Edge m}
    (hlegal : LegalMakerMove B e0) : (B.addMaker e0).Valid := by
  intro e h
  rcases h with ⟨hmaker, hbreaker⟩
  rcases hlegal with ⟨hvalid, hfree⟩
  rcases hmaker with hmaker | rfl
  · exact hvalid e ⟨hmaker, hbreaker⟩
  · exact hfree.2 hbreaker

theorem makerAvoidsVertex_addBreakerSet {m : Nat} {B : Board m}
    {D : Edge m -> Prop} {v : Fin m}
    (havoid : B.makerAvoidsVertex v) :
    (B.addBreakerSet D).makerAvoidsVertex v := by
  exact havoid

theorem makerAvoidsVertex_addMaker {m : Nat} {B : Board m}
    {e0 : Edge m} {v : Fin m}
    (havoid : B.makerAvoidsVertex v) (he0 : ¬ Edge.touches e0 v) :
    (B.addMaker e0).makerAvoidsVertex v := by
  intro e hmaker
  rcases hmaker with hmaker | rfl
  · exact havoid e hmaker
  · exact he0

namespace MakerReach

theorem addBreakerSet_iff {m : Nat} {B : Board m} {D : Edge m -> Prop}
    {u v : Fin m} :
    MakerReach (B.addBreakerSet D) u v ↔ MakerReach B u v := by
  constructor
  · intro h
    induction h with
    | refl v => exact MakerReach.refl v
    | step adj _ ih =>
        exact MakerReach.step (by
          simpa [Board.makerAdjacent, Board.addBreakerSet] using adj) ih
  · intro h
    induction h with
    | refl v => exact MakerReach.refl v
    | step adj _ ih =>
        exact MakerReach.step (by
          simpa [Board.makerAdjacent, Board.addBreakerSet] using adj) ih

theorem trans {m : Nat} {B : Board m} {u v w : Fin m}
    (huv : MakerReach B u v) (hvw : MakerReach B v w) :
    MakerReach B u w := by
  induction huv with
  | refl _ => exact hvw
  | step adj _ ih => exact MakerReach.step adj (ih hvw)

theorem of_adjacent {m : Nat} {B : Board m} {u v : Fin m}
    (hadj : B.makerAdjacent u v) : MakerReach B u v := by
  exact MakerReach.step hadj (MakerReach.refl v)

end MakerReach

namespace Board

variable {m : Nat}

/-- The current Maker component reachable from vertex `v`, as a finite set. -/
noncomputable def reachableFinset (B : Board m) (v : Fin m) : Finset (Fin m) :=
  by
    classical
    exact Finset.univ.filter (fun w => MakerReach B v w)

@[simp] theorem mem_reachableFinset {B : Board m} {v w : Fin m} :
    w ∈ B.reachableFinset v ↔ MakerReach B v w := by
  classical
  simp [reachableFinset]

theorem root_mem_reachableFinset (B : Board m) (v : Fin m) :
    v ∈ B.reachableFinset v := by
  rw [mem_reachableFinset]
  exact MakerReach.refl v

/-- If `u` is in the reachable component from `s`, and Maker owns an edge
from `u` to `v`, then `v` is in that component too. -/
theorem mem_reachableFinset_of_adjacent {B : Board m} {s u v : Fin m}
    (hu : u ∈ B.reachableFinset s) (hadj : B.makerAdjacent u v) :
    v ∈ B.reachableFinset s := by
  rw [mem_reachableFinset] at hu ⊢
  exact MakerReach.trans hu (MakerReach.of_adjacent hadj)

/-- No Maker-claimed edge can cross from a reachable component to its
complement. This is the formal version of "components are components." -/
theorem not_maker_edge_from_reachable_to_outside {B : Board m} {s u v : Fin m}
    (hu : u ∈ B.reachableFinset s) (hv : v ∉ B.reachableFinset s) :
    ¬ ∃ e, B.maker e ∧ Edge.incident e u v := by
  intro h
  rcases h with ⟨e, hmaker, hinc⟩
  exact hv (B.mem_reachableFinset_of_adjacent hu ⟨e, hmaker, hinc⟩)

theorem not_maker_of_incident_reachable_outside {B : Board m} {s : Fin m}
    {e : Edge m}
    (he : e ∈ Edge.fromSetToOutside (B.reachableFinset s) (B.reachableFinset s)) :
    ¬ B.maker e := by
  intro hmaker
  rw [Edge.mem_fromSetToOutside] at he
  rcases he with ⟨u, hu, v, hv, hinc⟩
  have hv_out : v ∉ B.reachableFinset s := by
    simpa using hv
  exact B.not_maker_edge_from_reachable_to_outside hu
    hv_out ⟨e, hmaker, hinc⟩

end Board

end NCop
