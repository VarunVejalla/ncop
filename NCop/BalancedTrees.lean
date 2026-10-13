import NCop.CutPairs
import NCop.InvariantStrategy
import NCop.Asymptotic
import Mathlib.Tactic

namespace NCop

namespace MakerReach

theorem reverse {m : Nat} {B : Board m} {u v : Fin m}
    (h : MakerReach B u v) : MakerReach B v u := by
  induction h with
  | refl v => exact .refl v
  | step adj _ ih =>
    obtain ⟨e, he, hu, hv, hne⟩ := adj
    exact ih.trans (.of_adjacent ⟨e, he, hv, hu, hne.symm⟩)

theorem claim_mono {m : Nat} {B : Board m} {e : Edge m} {u v : Fin m}
    (h : MakerReach B u v) : MakerReach (B.addMaker e) u v := by
  induction h with
  | refl v => exact .refl v
  | step adj _ ih =>
    obtain ⟨f, hf, hinc⟩ := adj
    exact .step ⟨f, Or.inl hf, hinc⟩ ih

end MakerReach

def Terminals.swap {m : Nat} (T : Terminals m) : Terminals m :=
  ⟨T.t, T.s, T.distinct.symm⟩

theorem makerHasPath_swap_iff {m : Nat} {T : Terminals m} {B : Board m} :
    MakerHasPath T.swap B ↔ MakerHasPath T B :=
  ⟨MakerReach.reverse, MakerReach.reverse⟩

/-- Explicit terminal trees. The confinement condition keeps every vertex
outside the two trees isolated in Maker's graph, so an expansion adds exactly
one vertex. The data are strategy witnesses, not a change to the game model. -/
structure BalancedTrees {m : Nat} (n : Nat) (T : Terminals m) (B : Board m) where
  r : Nat
  A : Finset (Fin m)
  C : Finset (Fin m)
  disjoint : Disjoint A C
  source : T.s ∈ A
  target : T.t ∈ C
  connectedA : ∀ v ∈ A, MakerReach B T.s v
  connectedC : ∀ v ∈ C, MakerReach B T.t v
  confined : ∀ e, B.maker e →
    (∀ v, Edge.touches e v → v ∈ A) ∨ (∀ v, Edge.touches e v → v ∈ C)
  balancedA : A.card ≤ C.card + 1
  balancedC : C.card ≤ A.card + 1
  sum_sizes : A.card + C.card = r + 2
  budget : AtMost (r * n) B.breaker
  valid : B.Valid

namespace BalancedTrees

def swap {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) : BalancedTrees n T.swap B where
  r := h.r
  A := h.C
  C := h.A
  disjoint := h.disjoint.symm
  source := h.target
  target := h.source
  connectedA := h.connectedC
  connectedC := h.connectedA
  confined := fun e he => (h.confined e he).symm
  balancedA := h.balancedC
  balancedC := h.balancedA
  sum_sizes := by rw [Nat.add_comm]; exact h.sum_sizes
  budget := h.budget
  valid := h.valid

theorem size_le {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) : h.A.card + h.C.card ≤ m := by
  classical
  have hc := Finset.card_le_univ (h.A ∪ h.C)
  rw [Finset.card_union_of_disjoint h.disjoint] at hc
  simpa using hc

/-- The balanced cut beats the total deletion budget for every `m >= 4n`.
This avoids a separate embedding or board-size monotonicity theorem. -/
theorem cut_margin {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) (hn : 1 ≤ n) (hm : 4 * n ≤ m)
    (hsmall : h.A.card ≤ h.C.card) :
    (h.r + 1) * n < h.A.card * (m - h.A.card) := by
  have hsum := h.sum_sizes
  have hbal := h.balancedC
  have htotal := h.size_le
  have hpos : 0 < h.A.card := by omega
  have hlower : h.r + 1 ≤ 2 * h.A.card := by omega
  have hspace : 2 * n ≤ m - h.A.card := by omega
  by_cases hstrict : h.r + 1 < 2 * h.A.card
  · have hmul := Nat.mul_lt_mul_of_pos_right hstrict (by omega : 0 < n)
    have hcut := Nat.mul_le_mul_left h.A.card hspace
    nlinarith
  · have heq : h.r + 1 = 2 * h.A.card := by omega
    have hspace' : 2 * n < m - h.A.card := by omega
    have hcut := Nat.mul_lt_mul_of_pos_left hspace' hpos
    nlinarith

/-- After any legal deletion, the smaller explicit tree has a free cut edge. -/
theorem free_cut_of_margin {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B)
    (hmargin : (h.r + 1) * n < h.A.card * (m - h.A.card)) {D : Edge m → Prop}
    (hD : LegalBreakerMove n B D) :
    ∃ e, e ∈ Edge.fromSetToOutside h.A h.A ∧ (B.addBreakerSet D).free e := by
  classical
  have hb : AtMost ((h.r + 1) * n) (B.addBreakerSet D).breaker := by
    simpa [Nat.add_mul] using Board.atMost_breaker_addBreakerSet h.budget hD
  apply Board.exists_free_edge_from_cutPairs_of_card_gt_breakerBudget hb
  · intro p hp
    have hmem := Edge.edgeOfCutPair_mem_fromSetToOutside p
    obtain ⟨u, hu, v, hv, hinc⟩ := Edge.mem_fromSetToOutside.mp hmem
    have hvout : v ∉ h.A := (Finset.mem_sdiff.mp hv).2
    rcases h.confined _ hp with hA | hC
    · exact hvout (hA v hinc.2.1)
    · exact Finset.disjoint_left.mp h.disjoint hu (hC u hinc.1)
  · exact hmargin

/-- Claim a cut edge: it either joins the terminal trees or adds a previously
unused vertex to the smaller tree while preserving every strategy condition. -/
theorem grow_of_margin {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B)
    (hmargin : (h.r + 1) * n < h.A.card * (m - h.A.card))
    (hsmall : h.A.card ≤ h.C.card) {D : Edge m → Prop}
    (hD : LegalBreakerMove n B D) :
    ∃ e, LegalMakerMove (B.addBreakerSet D) e ∧
      (MakerHasPath T ((B.addBreakerSet D).addMaker e) ∨
        ∃ hnew : BalancedTrees n T ((B.addBreakerSet D).addMaker e), hnew.r = h.r + 1) := by
  classical
  obtain ⟨e, hcut, hfree⟩ := h.free_cut_of_margin hmargin hD
  obtain ⟨u, hu, v, hv, hinc⟩ := Edge.mem_fromSetToOutside.mp hcut
  have hvA : v ∉ h.A := (Finset.mem_sdiff.mp hv).2
  have he : LegalMakerMove (B.addBreakerSet D) e :=
    ⟨Board.valid_after_legal_breaker hD, hfree⟩
  have hreachA : ∀ w ∈ h.A,
      MakerReach ((B.addBreakerSet D).addMaker e) T.s w := by
    intro w hw
    exact (MakerReach.addBreakerSet_iff.mpr (h.connectedA w hw)).claim_mono
  have hreachC : ∀ w ∈ h.C,
      MakerReach ((B.addBreakerSet D).addMaker e) T.t w := by
    intro w hw
    exact (MakerReach.addBreakerSet_iff.mpr (h.connectedC w hw)).claim_mono
  have hreachV : MakerReach ((B.addBreakerSet D).addMaker e) T.s v :=
    (hreachA u hu).trans (.of_adjacent ⟨e, Or.inr rfl, hinc⟩)
  refine ⟨e, he, ?_⟩
  by_cases hvC : v ∈ h.C
  · exact Or.inl (hreachV.trans (hreachC v hvC).reverse)
  · right
    refine ⟨{
      r := h.r + 1
      A := insert v h.A
      C := h.C
      disjoint := Finset.disjoint_insert_left.mpr ⟨hvC, h.disjoint⟩
      source := Finset.mem_insert_of_mem h.source
      target := h.target
      connectedA := ?_
      connectedC := hreachC
      confined := ?_
      balancedA := ?_
      balancedC := ?_
      sum_sizes := ?_
      budget := ?_
      valid := valid_addMaker he
    }, rfl⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hreachV
      · exact hreachA w hw
    · intro f hf
      rcases hf with hf | rfl
      · rcases h.confined f hf with hA | hC
        · exact Or.inl (fun w hw => Finset.mem_insert_of_mem (hA w hw))
        · exact Or.inr hC
      · left
        intro w hw
        have hcoe : (f : Sym2 (Fin m)) = s(u, v) :=
          Sym2.eq_of_ne_mem hinc.2.2 hinc.1 hinc.2.1
            (Sym2.mem_mk_left u v) (Sym2.mem_mk_right u v)
        rw [Edge.touches, hcoe, Sym2.mem_iff] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_insert_of_mem hu
        · exact Finset.mem_insert_self _ _
    · rw [Finset.card_insert_of_notMem hvA]
      omega
    · rw [Finset.card_insert_of_notMem hvA]
      have hbal := h.balancedC
      omega
    · rw [Finset.card_insert_of_notMem hvA]
      have hsum := h.sum_sizes
      omega
    · simpa [Nat.add_mul] using Board.atMost_breaker_addBreakerSet h.budget hD

/-- Original four-n cut interface. -/
theorem free_cut {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) (hn : 1 ≤ n) (hm : 4 * n ≤ m)
    (hsmall : h.A.card ≤ h.C.card) {D : Edge m → Prop}
    (hD : LegalBreakerMove n B D) :
    ∃ e, e ∈ Edge.fromSetToOutside h.A h.A ∧ (B.addBreakerSet D).free e :=
  h.free_cut_of_margin (h.cut_margin hn hm hsmall) hD

/-- Original four-n interface, obtained from the general cut-margin step. -/
theorem grow {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) (hn : 1 ≤ n) (hm : 4 * n ≤ m)
    (hsmall : h.A.card ≤ h.C.card) {D : Edge m → Prop}
    (hD : LegalBreakerMove n B D) :
    ∃ e, LegalMakerMove (B.addBreakerSet D) e ∧
      (MakerHasPath T ((B.addBreakerSet D).addMaker e) ∨
        Nonempty (BalancedTrees n T ((B.addBreakerSet D).addMaker e))) :=
by
  obtain ⟨e, he, hnext⟩ := h.grow_of_margin (h.cut_margin hn hm hsmall) hsmall hD
  refine ⟨e, he, ?_⟩
  rcases hnext with hw | ⟨hnew, _⟩
  · exact Or.inl hw
  · exact Or.inr ⟨hnew⟩

def initial {m n : Nat} (T : Terminals m) :
    BalancedTrees n T (Board.empty m) where
  r := 0
  A := {T.s}
  C := {T.t}
  disjoint := by simp [T.distinct]
  source := by simp
  target := by simp
  connectedA := by
    intro v hv
    have hv' : v = T.s := Finset.mem_singleton.mp hv
    subst v
    exact MakerReach.refl T.s
  connectedC := by
    intro v hv
    have hv' : v = T.t := Finset.mem_singleton.mp hv
    subst v
    exact MakerReach.refl T.t
  confined := by intro e he; exact False.elim he
  balancedA := by simp
  balancedC := by simp
  sum_sizes := by simp
  budget := ⟨[], by intro e he; exact False.elim he, by simp⟩
  valid := empty_valid m

end BalancedTrees

/-- The complete finite two-frontier winning theorem, with Breaker first. -/
theorem makerWins_of_four_mul_le {m n : Nat} (hn : 1 ≤ n) (hm : 4 * n ≤ m) :
    MakerWins m n := by
  intro T
  apply makerWinFrom_of_invariant T
    (fun B => Nonempty (BalancedTrees n T B))
    (fun _ h => h.some.valid)
  · intro B hInv _ D hD
    obtain ⟨h⟩ := hInv
    by_cases hsmall : h.A.card ≤ h.C.card
    · exact h.grow hn hm hsmall hD
    · obtain ⟨e, he, hnext⟩ := h.swap.grow hn hm (by
        exact Nat.le_of_lt (lt_of_not_ge hsmall)) hD
      refine ⟨e, he, ?_⟩
      rcases hnext with hwin | hnext
      · exact Or.inl (makerHasPath_swap_iff.mp hwin)
      · obtain ⟨hnew⟩ := hnext
        exact Or.inr ⟨hnew.swap⟩
  · exact ⟨BalancedTrees.initial T⟩

theorem makerUpperBound_four : MakerUpperBound 4 :=
  makerUpperBound_of_linear_wins 4 (fun _ _ hn hm => makerWins_of_four_mul_le hn hm)

end NCop
