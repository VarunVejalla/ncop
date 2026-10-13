import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace NCop

/-- Integer stopping size for the finite two-move lookahead strategy. -/
theorem lookahead_parameters {m n : Nat} (hn : 4 ≤ n)
    (hm : (2 + Real.sqrt 3) * (n : ℝ) ≤ m) :
    ∃ k : Nat, 1 ≤ k ∧ n ≤ k ∧ k ≤ 2*n ∧ k+2*n < m ∧ 2*k ≤ m ∧
      (2*k-1)*n < k*k + (m-2*k)*(2*(k-n)) := by
  let s : ℝ := Real.sqrt 3
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = 3 := Real.sq_sqrt (by norm_num)
  have hslo : (17:ℝ)/10 < s := by nlinarith
  have hshi : s < (18:ℝ)/10 := by nlinarith
  let x : ℝ := 1+s/3
  have hxlo : (3:ℝ)/2 < x := by dsimp [x]; linarith
  have hxhi : x < (8:ℝ)/5 := by dsimp [x]; linarith
  let k : Nat := ⌊x*(n:ℝ)⌋₊
  have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hklo : x*(n:ℝ)-1 < (k:ℝ) := by
    have := Nat.lt_floor_add_one (x*(n:ℝ))
    dsimp [k]; linarith
  have hkhi : (k:ℝ) ≤ x*(n:ℝ) := Nat.floor_le (by positivity)
  have hknR : (n:ℝ) ≤ k := by nlinarith
  have hk2R : (k:ℝ) ≤ 2*(n:ℝ) := by nlinarith
  have hspaceR : (k:ℝ)+2*(n:ℝ) < m := by
    change (2+s)*(n:ℝ) ≤ m at hm
    nlinarith
  have hnk : n ≤ k := by exact_mod_cast hknR
  have hk2 : k ≤ 2*n := by exact_mod_cast hk2R
  have hspace : k+2*n < m := by exact_mod_cast hspaceR
  have htotal : 2*k ≤ m := by omega
  have hdelta : 0 ≤ (m:ℝ)-(2+s)*(n:ℝ) := by
    change (2+s)*(n:ℝ) ≤ m at hm; linarith
  have herr : ((k:ℝ)-x*(n:ℝ))^2 ≤ 1 := by
    nlinarith [sq_nonneg ((k:ℝ)-x*(n:ℝ))]
  have hid : (k:ℝ)^2 + ((m:ℝ)-2*k)*(2*((k:ℝ)-n)) -
      (2*(k:ℝ)-1)*n = (n:ℝ)-3*((k:ℝ)-x*n)^2 +
        2*((m:ℝ)-(2+s)*n)*((k:ℝ)-n) := by
    dsimp [x]
    have hscaled : s^2 * (n:ℝ)^2 = 3*(n:ℝ)^2 := by rw [hs2]
    nlinarith [hscaled]
  have hprod : 0 ≤ ((m:ℝ)-(2+s)*n)*((k:ℝ)-n) :=
    mul_nonneg hdelta (by linarith)
  have hmarginR : (2*(k:ℝ)-1)*n <
      (k:ℝ)^2 + ((m:ℝ)-2*k)*(2*((k:ℝ)-n)) := by nlinarith
  refine ⟨k, by omega, hnk, hk2, hspace, htotal, ?_⟩
  have hkpos : 1 ≤ k := by omega
  have hcast : (((2*k-1)*n : Nat) : ℝ) <
      ((k*k + (m-2*k)*(2*(k-n)) : Nat) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2*k), Nat.cast_sub htotal,
      Nat.cast_sub hnk]
    nlinarith
  exact_mod_cast hcast

end NCop
