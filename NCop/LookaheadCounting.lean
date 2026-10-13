import NCop.BalancedTrees
import NCop.PartitionSafety

namespace NCop
open scoped Classical
namespace Edge

theorem eq_between_of_incident {m : Nat} {e : Edge m} {u v : Fin m}
    (h : incident e u v) : e = between u v h.2.2 := by
  apply Subtype.ext
  exact Sym2.eq_of_ne_mem h.2.2 h.1 h.2.1
    (Sym2.mem_mk_left u v) (Sym2.mem_mk_right u v)

theorem card_betweenSets {m : Nat} {A C : Finset (Fin m)}
    (hd : Disjoint A C) : (betweenSets A C).card = A.card * C.card := by
  classical
  symm
  rw [← Finset.card_product]
  let f : ∀ p ∈ A ×ˢ C, Edge m := fun p hp => between p.1 p.2 (by
    have h := Finset.mem_product.mp hp
    intro he
    exact Finset.disjoint_left.mp hd h.1 (he ▸ h.2))
  apply Finset.card_bij f
  · intro p hp
    obtain ⟨ha, hc⟩ := Finset.mem_product.mp hp
    exact mem_betweenSets.mpr ⟨p.1, ha, p.2, hc, incident_between _⟩
  · intro p hp q hq he
    have hs := congrArg (fun e : Edge m => (e : Sym2 (Fin m))) he
    change s(p.1,p.2) = s(q.1,q.2) at hs
    rw [Sym2.eq, Sym2.rel_iff] at hs
    rcases hs with hs | hs
    · exact Prod.ext hs.1 hs.2
    · exfalso
      exact Finset.disjoint_left.mp hd (Finset.mem_product.mp hp).1
        (hs.1 ▸ (Finset.mem_product.mp hq).2)
  · intro e he
    obtain ⟨u, hu, v, hv, hi⟩ := mem_betweenSets.mp he
    refine ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, ?_⟩
    exact (eq_between_of_incident hi).symm

theorem betweenSets_union_right {m : Nat} (X A C : Finset (Fin m)) :
    betweenSets X (A ∪ C) = betweenSets X A ∪ betweenSets X C := by
  classical
  ext e
  simp only [mem_betweenSets, Finset.mem_union]
  constructor
  · rintro ⟨u, hu, v, hv | hv, hi⟩
    · exact Or.inl ⟨u,hu,v,hv,hi⟩
    · exact Or.inr ⟨u,hu,v,hv,hi⟩
  · rintro (⟨u,hu,v,hv,hi⟩ | ⟨u,hu,v,hv,hi⟩)
    · exact ⟨u,hu,v,Or.inl hv,hi⟩
    · exact ⟨u,hu,v,Or.inr hv,hi⟩

theorem betweenSets_disjoint_right {m : Nat} {X A C : Finset (Fin m)}
    (hd : Disjoint A C) (hXA : Disjoint X A) :
    Disjoint (betweenSets X A) (betweenSets X C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨u,hu,v,hv,hi⟩ := mem_betweenSets.mp he
  obtain ⟨w,hw,z,hz,hj⟩ := mem_betweenSets.mp hf
  rcases incident_pairs hi hj with hs | hs
  · exact Finset.disjoint_left.mp hd hv (hs.2 ▸ hz)
  · exact Finset.disjoint_left.mp hXA hw (hs.2 ▸ hv)

end Edge

namespace Board

noncomputable def deletedTo {m : Nat} (B : Board m) (X : Finset (Fin m))
    (v : Fin m) : Finset (Edge m) :=
  (Edge.betweenSets {v} X).filter B.breaker

noncomputable def freeTo {m : Nat} (B : Board m) (X : Finset (Fin m))
    (v : Fin m) : Finset (Edge m) :=
  (Edge.betweenSets {v} X).filter B.free

theorem to_card_partition {m : Nat} {B : Board m} {X : Finset (Fin m)}
    {v : Fin m} (hv : v ∉ X)
    (hm : ∀ e ∈ Edge.betweenSets {v} X, ¬ B.maker e) :
    (B.deletedTo X v).card + (B.freeTo X v).card = X.card := by
  classical
  have hd : Disjoint ({v} : Finset (Fin m)) X := by simp [hv]
  have hf : B.freeTo X v = (Edge.betweenSets {v} X).filter (fun e => ¬ B.breaker e) := by
    ext e
    simp only [freeTo, Finset.mem_filter]
    constructor
    · rintro ⟨he, hf⟩; exact ⟨he, hf.2⟩
    · rintro ⟨he, hb⟩; exact ⟨he, hm e he, hb⟩
  rw [hf, deletedTo, Finset.card_filter_add_card_filter_not,
    Edge.card_betweenSets hd]
  simp

theorem deletedTo_union {m : Nat} (B : Board m) (A C : Finset (Fin m))
    (v : Fin m) : B.deletedTo (A ∪ C) v = B.deletedTo A v ∪ B.deletedTo C v := by
  classical
  simp [deletedTo, Edge.betweenSets_union_right, Finset.filter_union]

theorem deletedTo_pairwise {m : Nat} {B : Board m} {X O : Finset (Fin m)}
    (hd : Disjoint O X) : (O : Set (Fin m)).PairwiseDisjoint (B.deletedTo X) := by
  classical
  intro v hv w hw hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨u, hu, z, hz, hi⟩ := Edge.mem_betweenSets.mp (Finset.mem_filter.mp he).1
  obtain ⟨u', hu', z', hz', hj⟩ := Edge.mem_betweenSets.mp (Finset.mem_filter.mp hf).1
  have hu : u = v := Finset.mem_singleton.mp hu
  have hu' : u' = w := Finset.mem_singleton.mp hu'
  subst u; subst u'
  rcases Edge.incident_pairs hi hj with hs | hs
  · exact hne hs.1
  · exact Finset.disjoint_left.mp hd hv (hs.1 ▸ hz')

theorem cross_disjoint_deletedTo {m : Nat} {B : Board m} {A C : Finset (Fin m)}
    {v : Fin m} (hvA : v ∉ A) (hvC : v ∉ C) :
    Disjoint (Edge.betweenSets A C) (B.deletedTo (A ∪ C) v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨u, hu, w, hw, hi⟩ := Edge.mem_betweenSets.mp he
  obtain ⟨z, hz, y, _, hj⟩ := Edge.mem_betweenSets.mp (Finset.mem_filter.mp hf).1
  have hz : z = v := Finset.mem_singleton.mp hz
  subst z
  rcases Edge.incident_pairs hi hj with hs | hs
  · exact hvA (hs.1 ▸ hu)
  · exact hvC (hs.2 ▸ hw)

end Board

namespace BalancedTrees

theorem not_maker_cross {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) {e : Edge m} (he : e ∈ Edge.betweenSets h.A h.C) :
    ¬ B.maker e := by
  obtain ⟨u, hu, v, hv, hi⟩ := Edge.mem_betweenSets.mp he
  intro hm
  rcases h.confined e hm with hA | hC
  · exact Finset.disjoint_left.mp h.disjoint (hA v hi.2.1) hv
  · exact Finset.disjoint_left.mp h.disjoint hu (hC u hi.1)

theorem not_maker_outside {m n : Nat} {T : Terminals m} {B : Board m}
    (h : BalancedTrees n T B) {v : Fin m} (hv : v ∉ h.A ∪ h.C)
    {e : Edge m} (he : Edge.touches e v) : ¬ B.maker e := by
  intro hm
  rcases h.confined e hm with hA | hC
  · exact hv (Finset.mem_union_left _ (hA v he))
  · exact hv (Finset.mem_union_right _ (hC v he))

end BalancedTrees

/-- A budget contradiction at two equally sized terminal components.
The counted cross edges and outside-vertex fibers are disjoint. -/
theorem lookahead_budget {m n k q : Nat} {B : Board m}
    {A C : Finset (Fin m)} (hd : Disjoint A C)
    (ha : A.card = k) (hc : C.card = k) (hnk : n ≤ k) (hkn : k ≤ 2*n)
    (hb : AtMost q B.breaker)
    (hcross : ∀ e ∈ Edge.betweenSets A C, B.breaker e)
    (hmaker : ∀ v, v ∉ A ∪ C → ∀ e, Edge.touches e v → ¬ B.maker e)
    (hsafe : ∀ v, v ∉ A ∪ C →
      ((B.freeTo A v).card = 0 ∨ (B.freeTo C v).card ≤ n) ∧
      ((B.freeTo C v).card = 0 ∨ (B.freeTo A v).card ≤ n)) :
    k*k + (m-2*k)*(2*(k-n)) ≤ q := by
  classical
  let O := Finset.univ \ (A ∪ C)
  have ho : ∀ v ∈ O, v ∉ A ∪ C := by
    intro v hv; exact (Finset.mem_sdiff.mp hv).2
  have hod : Disjoint O (A ∪ C) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvin
    exact ho v hv hvin
  have hlocal : ∀ v ∈ O, 2*(k-n) ≤ (B.deletedTo (A ∪ C) v).card := by
    intro v hv
    have hvA : v ∉ A := fun hvA => ho v hv (Finset.mem_union_left _ hvA)
    have hvC : v ∉ C := fun hvC => ho v hv (Finset.mem_union_right _ hvC)
    have hma : ∀ e ∈ Edge.betweenSets {v} A, ¬ B.maker e := by
      intro e he
      obtain ⟨u,hu,w,_,hi⟩ := Edge.mem_betweenSets.mp he
      have hu : u=v := Finset.mem_singleton.mp hu
      exact hmaker v (ho v hv) e (hu ▸ hi.1)
    have hmc : ∀ e ∈ Edge.betweenSets {v} C, ¬ B.maker e := by
      intro e he
      obtain ⟨u,hu,w,_,hi⟩ := Edge.mem_betweenSets.mp he
      have hu : u=v := Finset.mem_singleton.mp hu
      exact hmaker v (ho v hv) e (hu ▸ hi.1)
    have hpa := B.to_card_partition hvA hma
    have hpc := B.to_card_partition hvC hmc
    rw [ha] at hpa; rw [hc] at hpc
    have hVA : Disjoint ({v} : Finset (Fin m)) A := by simp [hvA]
    have hdv : Disjoint (B.deletedTo A v) (B.deletedTo C v) :=
      (Edge.betweenSets_disjoint_right hd hVA).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [B.deletedTo_union, Finset.card_union_of_disjoint hdv]
    obtain ⟨h1,h2⟩ := hsafe v (ho v hv)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  let E := Edge.betweenSets A C ∪ O.biUnion (B.deletedTo (A ∪ C))
  have hEd : Disjoint (Edge.betweenSets A C) (O.biUnion (B.deletedTo (A ∪ C))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨v,hv,hf⟩ := Finset.mem_biUnion.mp hf
    have hdv := B.cross_disjoint_deletedTo
      (fun h => ho v hv (Finset.mem_union_left _ h))
      (fun h => ho v hv (Finset.mem_union_right _ h))
    exact Finset.disjoint_left.mp hdv he hf
  have hecard : E.card ≤ q := by
    apply finset_card_le_of_atMost hb
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hcross e he
    · obtain ⟨v,_,he⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp he).2
  have hOcard : O.card = m-2*k := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hd, ha, hc]
    simp; omega
  have hsum : O.card * (2*(k-n)) ≤ ∑ v ∈ O, (B.deletedTo (A ∪ C) v).card := by
    simpa using Finset.sum_le_sum hlocal
  dsimp [E] at hecard
  rw [Finset.card_union_of_disjoint hEd, Edge.card_betweenSets hd, ha, hc,
    Finset.card_biUnion (B.deletedTo_pairwise hod)] at hecard
  rw [hOcard] at hsum
  omega

end NCop
