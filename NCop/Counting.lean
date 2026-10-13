import NCop.Game

namespace NCop

open scoped Classical

namespace Edge

variable {m : Nat}

/-- The finite set of all game edges. -/
noncomputable def all (m : Nat) : Finset (Edge m) :=
  Finset.univ

/-- The finite set of game edges touching a vertex. -/
noncomputable def touching (v : Fin m) : Finset (Edge m) :=
  (all m).filter (fun e => Edge.touches e v)

@[simp] theorem mem_touching {v : Fin m} {e : Edge m} :
    e ∈ touching v ↔ Edge.touches e v := by
  classical
  simp [touching, all]

end Edge

namespace Board

variable {m : Nat}

/-- The finite set of currently free edges. -/
noncomputable def freeFinset (B : Board m) : Finset (Edge m) :=
  Finset.univ.filter (fun e => B.free e)

noncomputable def freeCount (B : Board m) : Nat :=
  (B.freeFinset).card

@[simp] theorem mem_freeFinset {B : Board m} {e : Edge m} :
    e ∈ B.freeFinset ↔ B.free e := by
  classical
  simp [freeFinset]

theorem freeCount_eq_card (B : Board m) :
    B.freeCount = B.freeFinset.card := rfl

theorem noFreeEdges_iff_freeFinset_empty {B : Board m} :
    B.noFreeEdges ↔ B.freeFinset = ∅ := by
  classical
  constructor
  · intro h
    ext e
    simp [h e]
  · intro h e he
    have : e ∈ B.freeFinset := by simp [he]
    rw [h] at this
    simp at this

theorem noFreeEdges_of_freeCount_eq_zero {B : Board m}
    (h : B.freeCount = 0) : B.noFreeEdges := by
  classical
  rw [noFreeEdges_iff_freeFinset_empty]
  exact Finset.card_eq_zero.mp h

/-- Edges in a finite candidate set that are not free on `B`. -/
noncomputable def forbiddenIn (B : Board m) (E : Finset (Edge m)) : Finset (Edge m) :=
  E.filter (fun e => ¬ B.free e)

@[simp] theorem mem_forbiddenIn {B : Board m} {E : Finset (Edge m)} {e : Edge m} :
    e ∈ B.forbiddenIn E ↔ e ∈ E ∧ ¬ B.free e := by
  classical
  simp [forbiddenIn]

/-- Pigeonhole form used by Maker proofs: if the set of forbidden candidate
edges is smaller than the candidate set, then some candidate edge is free. -/
theorem exists_free_of_forbidden_card_lt {B : Board m} {E : Finset (Edge m)}
    (hcard : (B.forbiddenIn E).card < E.card) :
    ∃ e, e ∈ E ∧ B.free e := by
  classical
  by_contra h
  have hsubset : E ⊆ B.forbiddenIn E := by
    intro e he
    have hnotfree : ¬ B.free e := by
      intro hfree
      exact h ⟨e, he, hfree⟩
    simp [he, hnotfree]
  have hle := Finset.card_le_card hsubset
  exact (not_lt_of_ge hle) hcard

end Board

namespace Edge

variable {m : Nat}

/-- Edges with one endpoint in `A` and one endpoint in `B`. -/
noncomputable def betweenSets (A B : Finset (Fin m)) : Finset (Edge m) :=
  (Edge.all m).filter fun e =>
    ∃ u ∈ A, ∃ v ∈ B, Edge.incident e u v

@[simp] theorem mem_betweenSets {A B : Finset (Fin m)} {e : Edge m} :
    e ∈ Edge.betweenSets A B ↔
      ∃ u ∈ A, ∃ v ∈ B, Edge.incident e u v := by
  classical
  simp [betweenSets, all]

/-- Edges from `A` to vertices outside `Used`. -/
noncomputable def fromSetToOutside (A Used : Finset (Fin m)) : Finset (Edge m) :=
  Edge.betweenSets A (Finset.univ \ Used)

@[simp] theorem mem_fromSetToOutside {A Used : Finset (Fin m)} {e : Edge m} :
    e ∈ Edge.fromSetToOutside A Used ↔
      ∃ u ∈ A, ∃ v ∈ (Finset.univ \ Used), Edge.incident e u v := by
  simp [fromSetToOutside]

end Edge

/-- A finite support bound immediately gives an `AtMost` witness. -/
theorem atMost_of_finset_support {α : Type u} [DecidableEq α]
    (P : α -> Prop) [DecidablePred P] (S : Finset α) (hS : ∀ x, P x -> x ∈ S)
    {k : Nat} (hcard : S.card <= k) : AtMost k P := by
  refine ⟨S.toList, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_toList.mpr (hS x hx)
  · simpa [Finset.length_toList] using hcard

/-- A predicate on a finite type is supported by its filtered universe. -/
theorem atMost_filter_univ {α : Type u} [Fintype α] [DecidableEq α]
    (P : α -> Prop) [DecidablePred P] {k : Nat}
    (hcard : (Finset.univ.filter P).card <= k) : AtMost k P := by
  exact atMost_of_finset_support P (Finset.univ.filter P)
    (by intro x hx; simp [hx]) hcard

/-- If a predicate is supported by at most `k` elements, then any finite set
whose elements satisfy the predicate has size at most `k`. -/
theorem finset_card_le_of_atMost {α : Type u} [DecidableEq α]
    {P : α -> Prop} {k : Nat} (hP : AtMost k P) (S : Finset α)
    (hS : ∀ x, x ∈ S -> P x) : S.card <= k := by
  rcases hP with ⟨xs, hxs, hlen⟩
  have hsub : S ⊆ xs.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (hxs x (hS x hx))
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le xs |>.trans hlen)

/-- Union of two supported predicates is supported by the sum of their
support sizes. -/
theorem atMost_or {α : Type u} {P Q : α -> Prop} {k l : Nat}
    (hP : AtMost k P) (hQ : AtMost l Q) :
    AtMost (k + l) (fun x => P x ∨ Q x) := by
  rcases hP with ⟨xs, hxs, hlenx⟩
  rcases hQ with ⟨ys, hys, hleny⟩
  refine ⟨xs ++ ys, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact List.mem_append_left _ (hxs x hx)
    · exact List.mem_append_right _ (hys x hx)
  · rw [List.length_append]
    exact Nat.add_le_add hlenx hleny

namespace Board

variable {m : Nat}

/-- Breaker deletion support after adding a legal deletion move. -/
theorem atMost_breaker_addBreakerSet {B : Board m} {D : Edge m -> Prop}
    {k n : Nat} (hB : AtMost k B.breaker) (hD : LegalBreakerMove n B D) :
    AtMost (k + n) (B.addBreakerSet D).breaker := by
  exact atMost_or hB hD.2.2

/-- If every candidate edge is not Maker-claimed and Breaker's whole deletion
set has support at most `k`, then the forbidden candidates have size at most
`k`. -/
theorem forbiddenIn_card_le_of_breaker_atMost {B : Board m} {E : Finset (Edge m)}
    {k : Nat} (hB : AtMost k B.breaker)
    (hnotMaker : ∀ e, e ∈ E -> ¬ B.maker e) :
    (B.forbiddenIn E).card <= k := by
  classical
  refine finset_card_le_of_atMost hB (B.forbiddenIn E) ?_
  intro e he
  rw [mem_forbiddenIn] at he
  rcases he with ⟨hE, hnotfree⟩
  by_contra hnotBreaker
  exact hnotfree ⟨hnotMaker e hE, hnotBreaker⟩

end Board

/-- The deletion set consisting of all edges touching one vertex has finite
support `Edge.touching v`. -/
theorem atMost_touching_of_card_le {m n : Nat} (v : Fin m)
    (hcard : (Edge.touching v).card <= n) :
    AtMost n (fun e : Edge m => Edge.touches e v) := by
  classical
  exact atMost_of_finset_support (fun e : Edge m => Edge.touches e v)
    (Edge.touching v) (by intro e he; simpa [Edge.mem_touching] using he) hcard

namespace Edge

/-- A concrete list of all edges touching `v`, one for each other vertex. -/
noncomputable def touchingList {m : Nat} (v : Fin m) : List (Edge m) :=
  ((Finset.univ.erase v).attach.toList.map fun w =>
    Edge.between v w.1 (by
      intro hvw
      exact (Finset.mem_erase.mp w.2).1 hvw.symm))

theorem mem_touchingList_of_touches {m : Nat} {v : Fin m} {e : Edge m}
    (he : Edge.touches e v) : e ∈ Edge.touchingList v := by
  classical
  let w : Fin m := Sym2.Mem.other he
  have hw_ne : w ≠ v := by
    have hnotdiag : ¬ (e : Sym2 (Fin m)).IsDiag :=
      SimpleGraph.not_isDiag_of_mem_edgeSet (G := (⊤ : SimpleGraph (Fin m))) e.property
    exact Sym2.other_ne hnotdiag he
  have hw_mem : w ∈ Finset.univ.erase v := by
    exact Finset.mem_erase.mpr ⟨hw_ne, Finset.mem_univ w⟩
  rw [touchingList, List.mem_map]
  refine ⟨⟨w, hw_mem⟩, ?_, ?_⟩
  · exact Finset.mem_toList.mpr (Finset.mem_attach _ _)
  apply Subtype.ext
  exact Sym2.other_spec he

theorem length_touchingList {m : Nat} (v : Fin m) :
    (Edge.touchingList v).length = m - 1 := by
  classical
  rw [touchingList, List.length_map, Finset.length_toList]
  simp

/-- There are at most `m - 1` edges touching a fixed vertex. -/
theorem atMost_touching {m : Nat} (v : Fin m) :
    AtMost (m - 1) (fun e : Edge m => Edge.touches e v) := by
  refine ⟨Edge.touchingList v, ?_, ?_⟩
  · intro e he
    exact Edge.mem_touchingList_of_touches he
  · rw [Edge.length_touchingList]

end Edge

end NCop
