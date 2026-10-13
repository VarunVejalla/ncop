import Mathlib.Combinatorics.Matroid.Circuit

namespace NCop

/-- The local exchange step in the Bednarska--Pikhurko Breaker strategy.
`P` is the protected Maker set; its new claim `e` is known to be safe in
at least one covering set. Every other independent covering set can absorb
`e`, either immediately or by removing one element outside `P` and `e`.

Source: Biased positional games on matroids (2005), Theorem 2. This lemma
proves the exchange step using Mathlib's fundamental-circuit API; it does
not assume the paper's strategy theorem as an axiom. -/
theorem matroid_exists_repair_outside_protected {α : Type*}
    {M : Matroid α} {I P : Set α} {e : α}
    (hI : M.Indep I) (hP : M.Indep (insert e P)) (he : e ∈ M.E) :
    M.Indep (insert e I) ∨
      ∃ x ∈ I, x ∉ P ∧ x ≠ e ∧ M.Indep (insert e I \ {x}) := by
  classical
  by_cases hnew : M.Indep (insert e I)
  · exact Or.inl hnew
  · right
    have heI : e ∉ I := by
      intro hei
      exact hnew (by simpa [Set.insert_eq_of_mem hei] using hI)
    have hecl : e ∈ M.closure I :=
      hI.mem_closure_iff.mpr (Or.inl ⟨hnew, Set.insert_subset he hI.subset_ground⟩)
    have hC := hI.fundCircuit_isCircuit hecl heI
    have hout : ∃ x ∈ M.fundCircuit e I, x ∉ insert e P := by
      by_contra hnone
      apply hC.not_indep
      apply hP.subset
      intro x hx
      by_contra hxnot
      exact hnone ⟨x, hx, hxnot⟩
    obtain ⟨x, hx, hxnot⟩ := hout
    have hxe : x ≠ e := by
      intro hxe
      exact hxnot (hxe ▸ Set.mem_insert e P)
    have hxP : x ∉ P := fun h => hxnot (Set.mem_insert_of_mem e h)
    have hxI : x ∈ I := by
      rcases M.fundCircuit_subset_insert e I hx with hxe' | hxI
      · exact False.elim (hxe hxe')
      · exact hxI
    exact ⟨x, hxI, hxP, hxe, (hI.mem_fundCircuit_iff hecl heI).mp hx⟩

end NCop
