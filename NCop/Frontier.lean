import NCop.CutPairs
import NCop.Lemmas

namespace NCop

namespace Board

variable {m : Nat}

/-- Candidate progress edges leaving the current Maker component reachable from
`s`. If one is free, Maker can either connect to the target component or grow
the source component. -/
noncomputable def sourceFrontier (B : Board m) (s : Fin m) : Finset (Edge m) :=
  Edge.fromSetToOutside (B.reachableFinset s) (B.reachableFinset s)

@[simp] theorem mem_sourceFrontier {B : Board m} {s : Fin m} {e : Edge m} :
    e ∈ B.sourceFrontier s ↔
      ∃ u ∈ B.reachableFinset s,
        ∃ v ∈ (Finset.univ \ B.reachableFinset s), Edge.incident e u v := by
  simp [sourceFrontier]

theorem not_maker_of_mem_sourceFrontier {B : Board m} {s : Fin m} {e : Edge m}
    (he : e ∈ B.sourceFrontier s) : ¬ B.maker e := by
  exact B.not_maker_of_incident_reachable_outside he

/-- If the source frontier has more edges than Breaker's entire deletion
support, then some source-frontier edge is free. -/
theorem exists_free_sourceFrontier_of_card_gt_breakerBudget
    {B : Board m} {s : Fin m} {k : Nat}
    (hbreaker : AtMost k B.breaker)
    (hcard : k < (B.sourceFrontier s).card) :
    ∃ e, e ∈ B.sourceFrontier s ∧ B.free e := by
  classical
  have hforbid :
      (B.forbiddenIn (B.sourceFrontier s)).card <= k :=
    B.forbiddenIn_card_le_of_breaker_atMost hbreaker
      (by
        intro e he
        exact B.not_maker_of_mem_sourceFrontier he)
  exact B.exists_free_of_forbidden_card_lt (lt_of_le_of_lt hforbid hcard)

/-- Counting form of source-frontier progress using ordered cut pairs. If
`|C_s| * (m - |C_s|)` beats Breaker's deletion support, then some edge leaving
the source component is free. -/
theorem exists_free_sourceFrontier_of_mul_gt_breakerBudget
    {B : Board m} {s : Fin m} {k : Nat}
    (hbreaker : AtMost k B.breaker)
    (hcard : k < (B.reachableFinset s).card * (m - (B.reachableFinset s).card)) :
    ∃ e, e ∈ B.sourceFrontier s ∧ B.free e := by
  classical
  rcases B.exists_free_edge_from_cutPairs_of_card_gt_breakerBudget
      (A := B.reachableFinset s) hbreaker
      (by
        intro p
        exact B.not_maker_of_incident_reachable_outside
          (Edge.edgeOfCutPair_mem_fromSetToOutside p))
      hcard with ⟨e, he, hfree⟩
  exact ⟨e, by simpa [sourceFrontier] using he, hfree⟩

end Board

end NCop
