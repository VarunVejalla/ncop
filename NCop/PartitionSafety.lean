import NCop.MatroidStrategy
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Logic.Function.Iterate

namespace NCop

theorem Edge.incident_pairs {m : Nat} {e : Edge m} {a b u v : Fin m}
    (hab : Edge.incident e a b) (huv : Edge.incident e u v) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  have h₁ : (e : Sym2 (Fin m)) = s(a, b) :=
    Sym2.eq_of_ne_mem hab.2.2 hab.1 hab.2.1
      (Sym2.mem_mk_left a b) (Sym2.mem_mk_right a b)
  have h₂ : (e : Sym2 (Fin m)) = s(u, v) :=
    Sym2.eq_of_ne_mem huv.2.2 huv.1 huv.2.1
      (Sym2.mem_mk_left u v) (Sym2.mem_mk_right u v)
  exact Sym2.rel_iff.mp (Sym2.eq.mp (h₁.symm.trans h₂))

/-- An orientation with terminal sinks and at most one claimed outgoing edge
per vertex cannot contain a claimed terminal path. Cycles away from the
terminals are allowed, so a partition matroid suffices. -/
theorem no_path_of_injective_tails {m : Nat} (T : Terminals m)
    (tail head : Edge m → Fin m)
    (hinc : ∀ e, Edge.incident e (tail e) (head e))
    (B : Board m)
    (hinj : Set.InjOn tail {e | B.maker e})
    (hsinks : ∀ e, B.maker e → tail e ≠ T.s ∧ tail e ≠ T.t) :
    ¬ MakerHasPath T B := by
  classical
  let next : Fin m → Fin m := fun u =>
    if h : ∃ e, B.maker e ∧ tail e = u then head (Classical.choose h) else u
  have hnext : ∀ e, B.maker e → next (tail e) = head e := by
    intro e he
    have hex : ∃ f, B.maker f ∧ tail f = tail e := ⟨e, he, rfl⟩
    simp only [next, dif_pos hex]
    have hc := Classical.choose_spec hex
    exact congrArg head (hinj hc.1 he hc.2)
  have hs : next T.s = T.s := by
    have hnone : ¬ ∃ e, B.maker e ∧ tail e = T.s := by
      rintro ⟨e, he, htail⟩
      exact (hsinks e he).1 htail
    simp only [next, dif_neg hnone]
  let reaches : Fin m → Prop := fun u => ∃ k : Nat, next^[k] u = T.t
  have hback : ∀ e, B.maker e → reaches (head e) → reaches (tail e) := by
    intro e he ⟨k, hk⟩
    exact ⟨k + 1, by simpa [Function.iterate_succ_apply, hnext e he] using hk⟩
  have hforward : ∀ e, B.maker e → reaches (tail e) → reaches (head e) := by
    intro e he ⟨k, hk⟩
    cases k with
    | zero => exact False.elim ((hsinks e he).2 hk)
    | succ k =>
      exact ⟨k, by simpa [Function.iterate_succ_apply, hnext e he] using hk⟩
  have hadj : ∀ {u v}, B.makerAdjacent u v → reaches v → reaches u := by
    intro u v ⟨e, he, heinc⟩ hv
    rcases Edge.incident_pairs (hinc e) heinc with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · simpa [ht] using hback e he (by simpa [hh] using hv)
    · simpa [hh] using hforward e he (by simpa [ht] using hv)
  have hreach : ∀ {u v}, MakerReach B u v → v = T.t → reaches u := by
    intro u v hr
    induction hr with
    | refl v => intro hv; subst v; exact ⟨0, rfl⟩
    | step adj _ ih => intro hv; exact hadj adj (ih hv)
  intro hp
  obtain ⟨k, hk⟩ := hreach hp rfl
  exact T.distinct ((Function.iterate_fixed hs k).symm.trans hk)

/-- A finite orientation certificate uses a color injective within each
outgoing fiber. This gives a cover by independent sets of a partition matroid. -/
structure SinkOrientation {m : Nat} (T : Terminals m) (k : Nat) where
  tail : Edge m → Fin m
  head : Edge m → Fin m
  incident : ∀ e, Edge.incident e (tail e) (head e)
  ordinary : ∀ e, e ≠ Edge.between T.s T.t T.distinct →
    tail e ≠ T.s ∧ tail e ≠ T.t
  color : Edge m → Fin k
  injective : ∀ e f,
    e ≠ Edge.between T.s T.t T.distinct →
    f ≠ Edge.between T.s T.t T.distinct →
    tail e = tail f → color e = color f → e = f

namespace SinkOrientation

noncomputable def certificate {m n : Nat} {T : Terminals m}
    (h : SinkOrientation T (n + 1)) (hn : 1 ≤ n) : MatroidLowerCertificate n T := by
  classical
  let terminals : Set (Fin m) := {u | u ≠ T.s ∧ u ≠ T.t}
  let M : Matroid (Edge m) := (Matroid.freeOn terminals).comap h.tail
  let edge := Edge.between T.s T.t T.distinct
  let D : Edge m → Prop := fun e => e = edge
  refine {
    matroid := M
    opening := D
    legal := ?_
    cover := ?_
    safe := ?_
  }
  · refine ⟨empty_valid m, ?_, ?_⟩
    · intro e _; exact ⟨not_false, not_false⟩
    · exact ⟨[edge], by intro e he; simpa [D] using he, by simpa using hn⟩
  · refine ⟨{
      sets := fun i => {e | e ≠ edge ∧ h.color e = i}
      indep := ?_
      common := ?_
      covered := ?_
      undeleted := ?_
    }⟩
    · intro i
      rw [Matroid.comap_indep_iff, Matroid.freeOn_indep_iff]
      constructor
      · rintro u ⟨e, he, rfl⟩
        exact h.ordinary e he.1
      · intro e he f hf htail
        exact h.injective e f he.1 hf.1 htail (he.2.trans hf.2.symm)
    · intro i e he; exact False.elim he
    · intro e he
      refine ⟨h.color e, ?_, rfl⟩
      intro heedge
      exact he.2 (Or.inr heedge)
    · intro i e he hdel
      rcases hdel with hdel | hdel
      · exact False.elim hdel
      · exact he.1 hdel
  · intro B hI
    rw [Matroid.comap_indep_iff, Matroid.freeOn_indep_iff] at hI
    apply no_path_of_injective_tails T h.tail h.head h.incident B hI.2
    intro e he
    exact hI.1 ⟨e, he, rfl⟩

end SinkOrientation

end NCop
