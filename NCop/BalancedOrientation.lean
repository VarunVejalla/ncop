import NCop.PartitionSafety
import Mathlib.Tactic

namespace NCop

/-- A balanced tournament: the smaller endpoint points to the larger when
their parities agree; otherwise the larger points to the smaller. -/
def parityPreference {m : Nat} (u v : Fin m) : Prop :=
  u.val < v.val ↔ u.val % 2 = v.val % 2

theorem parityPreference_reverse {m : Nat} {u v : Fin m} (hne : u ≠ v) :
    parityPreference v u ↔ ¬ parityPreference u v := by
  have hval : u.val ≠ v.val := fun heq => hne (Fin.ext heq)
  unfold parityPreference
  omega

/-- Outgoing neighbors of one vertex have distinct half-indices. This gives
an explicit fiber coloring without a graph-arboricity theorem. -/
theorem parityPreference_half_injective {m : Nat} {u v w : Fin m}
    (huv : u ≠ v) (huw : u ≠ w)
    (hv : parityPreference u v) (hw : parityPreference u w)
    (heq : v.val / 2 = w.val / 2) : v = w := by
  have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have huw' : u.val ≠ w.val := fun h => huw (Fin.ext h)
  apply Fin.ext
  unfold parityPreference at hv hw
  omega

namespace Edge

noncomputable def endpoints {m : Nat} (e : Edge m) : Fin m × Fin m :=
  (e : Sym2 (Fin m)).out

theorem endpoints_incident {m : Nat} (e : Edge m) :
    Edge.incident e (Edge.endpoints e).1 (Edge.endpoints e).2 := by
  refine ⟨Sym2.out_fst_mem _, Sym2.out_snd_mem _, ?_⟩
  have hrepr : s((Edge.endpoints e).1, (Edge.endpoints e).2) = (e : Sym2 (Fin m)) := by
    rw [endpoints, Sym2.mk, Quot.out_eq]
  intro heq
  have hd := SimpleGraph.not_isDiag_of_mem_edgeSet
    (G := (⊤ : SimpleGraph (Fin m))) e.property
  apply hd
  rw [← hrepr]
  simp [heq]

theorem eq_between_of_touches {m : Nat} {e : Edge m} {u v : Fin m} (hne : u ≠ v)
    (hu : Edge.touches e u) (hv : Edge.touches e v) :
    e = Edge.between u v hne := by
  apply Subtype.ext
  exact (Sym2.mem_and_mem_iff hne).mp ⟨hu, hv⟩

end Edge

/-- Terminal edges point into the terminal; all other edges use the balanced
tournament. The direct terminal edge will be deleted on the opening move. -/
noncomputable def terminalOrientation {m : Nat} (T : Terminals m) (e : Edge m) :
    Fin m × Fin m := by
  classical
  exact if hs : Edge.touches e T.s then (Sym2.Mem.other hs, T.s)
    else if ht : Edge.touches e T.t then (Sym2.Mem.other ht, T.t)
    else if parityPreference (Edge.endpoints e).1 (Edge.endpoints e).2 then Edge.endpoints e
    else (Edge.endpoints e).swap

namespace terminalOrientation

theorem incident {m : Nat} (T : Terminals m) (e : Edge m) :
    Edge.incident e (terminalOrientation T e).1 (terminalOrientation T e).2 := by
  classical
  have hnd := SimpleGraph.not_isDiag_of_mem_edgeSet
    (G := (⊤ : SimpleGraph (Fin m))) e.property
  unfold terminalOrientation
  split_ifs with hs ht hp
  · exact ⟨Sym2.other_mem hs, hs, Sym2.other_ne hnd hs⟩
  · exact ⟨Sym2.other_mem ht, ht, Sym2.other_ne hnd ht⟩
  · exact Edge.endpoints_incident e
  · obtain ⟨ha, hb, hne⟩ := Edge.endpoints_incident e
    exact ⟨hb, ha, hne.symm⟩

theorem ordinary_tail {m : Nat} (T : Terminals m) (e : Edge m)
    (he : e ≠ Edge.between T.s T.t T.distinct) :
    (terminalOrientation T e).1 ≠ T.s ∧ (terminalOrientation T e).1 ≠ T.t := by
  classical
  have hi := incident T e
  by_cases hs : Edge.touches e T.s
  · have hh : (terminalOrientation T e).2 = T.s := by
      simp [terminalOrientation, hs]
    refine ⟨fun htail => hi.2.2 (htail.trans hh.symm), ?_⟩
    intro htail
    exact he (Edge.eq_between_of_touches T.distinct hs (htail ▸ hi.1))
  · refine ⟨fun htail => hs (htail ▸ hi.1), ?_⟩
    by_cases ht : Edge.touches e T.t
    · have hh : (terminalOrientation T e).2 = T.t := by
        simp [terminalOrientation, hs, ht]
      exact fun htail => hi.2.2 (htail.trans hh.symm)
    · exact fun htail => ht (htail ▸ hi.1)

theorem preference_of_ordinary_head {m : Nat} (T : Terminals m) (e : Edge m)
    (hs : (terminalOrientation T e).2 ≠ T.s)
    (ht : (terminalOrientation T e).2 ≠ T.t) :
    parityPreference (terminalOrientation T e).1 (terminalOrientation T e).2 := by
  classical
  unfold terminalOrientation at hs ht ⊢
  split_ifs at hs ht ⊢ with hes het hp
  · exact False.elim (hs rfl)
  · exact False.elim (ht rfl)
  · exact hp
  · exact (parityPreference_reverse (Edge.endpoints_incident e).2.2).mpr hp

end terminalOrientation

/-- Reserve two extra colors for edges into the terminals; the remaining
colors are the balanced tournament's neighbor half-indices. -/
noncomputable def orientationColor {m : Nat} (T : Terminals m) (e : Edge m) : Nat := by
  classical
  let v := (terminalOrientation T e).2
  exact if v = T.s then (m + 1) / 2
    else if v = T.t then (m + 1) / 2 + 1 else v.val / 2

theorem orientationColor_lt {m : Nat} (T : Terminals m) (e : Edge m) :
    orientationColor T e < (m + 1) / 2 + 2 := by
  classical
  unfold orientationColor
  dsimp only
  split_ifs with hs ht
  · omega
  · omega
  · have hv := (terminalOrientation T e).2.isLt
    omega

theorem orientationColor_injective {m : Nat} (T : Terminals m) (e f : Edge m)
    (htail : (terminalOrientation T e).1 = (terminalOrientation T f).1)
    (hcolor : orientationColor T e = orientationColor T f) : e = f := by
  classical
  have heinc := terminalOrientation.incident T e
  have hfinc := terminalOrientation.incident T f
  have hhead : (terminalOrientation T e).2 = (terminalOrientation T f).2 := by
    let ve := (terminalOrientation T e).2
    let vf := (terminalOrientation T f).2
    have hve : ve.val / 2 < (m + 1) / 2 := by have hv := ve.isLt; omega
    have hvf : vf.val / 2 < (m + 1) / 2 := by have hv := vf.isLt; omega
    change ve = vf
    change (if ve = T.s then (m+1)/2 else if ve = T.t then (m+1)/2+1 else ve.val/2) =
      (if vf = T.s then (m+1)/2 else if vf = T.t then (m+1)/2+1 else vf.val/2) at hcolor
    by_cases hes : ve = T.s
    · by_cases hfs : vf = T.s
      · exact hes.trans hfs.symm
      · by_cases hft : vf = T.t
        · simp only [if_pos hes, if_neg hfs, if_pos hft] at hcolor
          omega
        · simp only [if_pos hes, if_neg hfs, if_neg hft] at hcolor
          omega
    · by_cases het : ve = T.t
      · by_cases hft : vf = T.t
        · exact het.trans hft.symm
        · by_cases hfs : vf = T.s
          · simp only [if_neg hes, if_pos het, if_pos hfs] at hcolor
            omega
          · simp only [if_neg hes, if_pos het, if_neg hfs, if_neg hft] at hcolor
            omega
      · by_cases hfs : vf = T.s
        · simp only [if_neg hes, if_neg het, if_pos hfs] at hcolor
          omega
        · by_cases hft : vf = T.t
          · simp only [if_neg hes, if_neg het, if_neg hfs, if_pos hft] at hcolor
            omega
          · simp only [if_neg hes, if_neg het, if_neg hfs, if_neg hft] at hcolor
            apply parityPreference_half_injective heinc.2.2
              (by simpa [htail] using hfinc.2.2)
              (terminalOrientation.preference_of_ordinary_head T e hes het)
              (by simpa [htail] using
                terminalOrientation.preference_of_ordinary_head T f hfs hft) hcolor
  apply Subtype.ext
  have heq := (Sym2.mem_and_mem_iff heinc.2.2).mp ⟨heinc.1, heinc.2.1⟩
  have hfq := (Sym2.mem_and_mem_iff hfinc.2.2).mp ⟨hfinc.1, hfinc.2.1⟩
  exact heq.trans (by simpa [htail, hhead] using hfq.symm)

noncomputable def balancedSinkOrientation {m n : Nat} (T : Terminals m)
    (hbound : (m + 1) / 2 + 2 ≤ n + 1) : SinkOrientation T (n + 1) where
  tail := fun e => (terminalOrientation T e).1
  head := fun e => (terminalOrientation T e).2
  incident := terminalOrientation.incident T
  ordinary := terminalOrientation.ordinary_tail T
  color := fun e => ⟨orientationColor T e, (orientationColor_lt T e).trans_le hbound⟩
  injective := fun e f _ _ htail hcolor =>
    orientationColor_injective T e f htail (congrArg Fin.val hcolor)

end NCop
