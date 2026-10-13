import NCop.Counting
import NCop.Lemmas

namespace NCop

namespace Edge

variable {m : Nat}

/-- Ordered vertex pairs crossing from `A` to its complement. These are the
objects counted by `|A| * (m - |A|)` in the informal proof. -/
noncomputable def cutPairs (A : Finset (Fin m)) : Finset (Fin m × Fin m) :=
  A ×ˢ (Finset.univ \ A)

@[simp] theorem mem_cutPairs {A : Finset (Fin m)} {p : Fin m × Fin m} :
    p ∈ Edge.cutPairs A ↔ p.1 ∈ A ∧ p.2 ∈ (Finset.univ \ A) := by
  simp [cutPairs]

theorem cutPair_ne {A : Finset (Fin m)} {p : Fin m × Fin m}
    (hp : p ∈ Edge.cutPairs A) : p.1 ≠ p.2 := by
  rw [Edge.mem_cutPairs] at hp
  intro h
  have hp2_not : p.2 ∉ A := by
    simpa [Finset.mem_sdiff] using hp.2
  exact hp2_not (h ▸ hp.1)

/-- The undirected edge determined by an ordered cut pair. -/
noncomputable def edgeOfCutPair {A : Finset (Fin m)}
    (p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A}) : Edge m :=
  Edge.between p.val.1 p.val.2 (Edge.cutPair_ne p.property)

@[simp] theorem edgeOfCutPair_coe {A : Finset (Fin m)}
    (p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A}) :
    ((Edge.edgeOfCutPair (m := m) p : Edge m) : Sym2 (Fin m)) =
      s(p.val.1, p.val.2) := by
  simp [edgeOfCutPair, Edge.between]

theorem edgeOfCutPair_injective {A : Finset (Fin m)} :
    Function.Injective (Edge.edgeOfCutPair (m := m) (A := A)) := by
  classical
  intro p q hpq
  apply Subtype.ext
  have hp := p.property
  have hq := q.property
  rw [Edge.mem_cutPairs] at hp hq
  have hsym : s(p.val.1, p.val.2) = s(q.val.1, q.val.2) := by
    have hcoerce := congrArg (fun e : Edge m => (e : Sym2 (Fin m))) hpq
    simpa using hcoerce
  rw [Sym2.eq, Sym2.rel_iff] at hsym
  rcases hsym with hsame | hswap
  · exact Prod.ext hsame.1 hsame.2
  · exfalso
    have hq1_not : q.val.1 ∉ Finset.univ \ A := by
      intro h
      have hnotA : q.val.1 ∉ A := by
        simpa [Finset.mem_sdiff] using h
      exact hnotA hq.1
    exact hq1_not (hswap.2 ▸ hp.2)

theorem card_cutPairs (A : Finset (Fin m)) :
    (Edge.cutPairs A).card = A.card * (m - A.card) := by
  classical
  have hcard : (Finset.univ \ A).card = m - A.card := by
    simpa using Finset.card_sdiff_of_subset (s := A) (t := Finset.univ)
      (by intro x _; exact Finset.mem_univ x)
  simp [Edge.cutPairs, Finset.card_product, hcard]

theorem edgeOfCutPair_mem_fromSetToOutside {A : Finset (Fin m)}
    (p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A}) :
    Edge.edgeOfCutPair (m := m) p ∈ Edge.fromSetToOutside A A := by
  classical
  have hp := p.property
  rw [Edge.mem_cutPairs] at hp
  rw [Edge.mem_fromSetToOutside]
  exact ⟨p.val.1, hp.1, p.val.2, hp.2, by simp [Edge.edgeOfCutPair]⟩

end Edge

namespace Board

variable {m : Nat}

/-- Cut pairs whose corresponding edge is forbidden. -/
noncomputable def forbiddenCutPairs (B : Board m) (A : Finset (Fin m)) :
    Finset {p : Fin m × Fin m // p ∈ Edge.cutPairs A} :=
  by
    classical
    exact Finset.univ.filter fun p => ¬ B.free (Edge.edgeOfCutPair p)

theorem forbiddenCutPairs_card_le_of_breaker_atMost
    {B : Board m} {A : Finset (Fin m)} {k : Nat}
    (hbreaker : AtMost k B.breaker)
    (hnotMaker : ∀ p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A},
      ¬ B.maker (Edge.edgeOfCutPair p)) :
    (B.forbiddenCutPairs A).card <= k := by
  classical
  rcases hbreaker with ⟨xs, hxs, hlen⟩
  let support : Finset (Edge m) := xs.toFinset
  have hmap : Set.MapsTo
      (fun p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A} => Edge.edgeOfCutPair p)
      ↑(B.forbiddenCutPairs A) ↑support := by
    intro p hp
    have hp_forbid : ¬ B.free (Edge.edgeOfCutPair p) := by
      simpa [forbiddenCutPairs] using hp
    have hbr : B.breaker (Edge.edgeOfCutPair p) := by
      by_contra hnotbr
      exact hp_forbid ⟨hnotMaker p, hnotbr⟩
    exact List.mem_toFinset.mpr (hxs _ hbr)
  have hinj : Set.InjOn
      (fun p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A} => Edge.edgeOfCutPair p)
      ↑(B.forbiddenCutPairs A) := by
    intro p _ q _ hpq
    exact Edge.edgeOfCutPair_injective hpq
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
    (List.toFinset_card_le xs |>.trans hlen)

theorem exists_free_edge_from_cutPairs_of_card_gt_breakerBudget
    {B : Board m} {A : Finset (Fin m)} {k : Nat}
    (hbreaker : AtMost k B.breaker)
    (hnotMaker : ∀ p : {p : Fin m × Fin m // p ∈ Edge.cutPairs A},
      ¬ B.maker (Edge.edgeOfCutPair p))
    (hcard : k < A.card * (m - A.card)) :
    ∃ e, e ∈ Edge.fromSetToOutside A A ∧ B.free e := by
  classical
  by_contra hnone
  have hall_forbid : (B.forbiddenCutPairs A) = Finset.univ := by
    ext p
    simp [forbiddenCutPairs]
    intro hfree
    exact hnone ⟨Edge.edgeOfCutPair p,
      Edge.edgeOfCutPair_mem_fromSetToOutside p, hfree⟩
  have hforbid := B.forbiddenCutPairs_card_le_of_breaker_atMost hbreaker hnotMaker
  rw [hall_forbid] at hforbid
  have hdomain :
      (Finset.univ : Finset {p : Fin m × Fin m // p ∈ Edge.cutPairs A}).card =
        (Edge.cutPairs A).card := by
    rw [Finset.card_univ]
    exact Fintype.card_ofFinset (Edge.cutPairs A) (by intro x; rfl)
  rw [hdomain, Edge.card_cutPairs] at hforbid
  exact (not_lt_of_ge hforbid) hcard

end Board

end NCop
