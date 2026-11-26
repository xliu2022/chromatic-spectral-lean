module

public import ChromaticSpectral.OneSignChange

/-! # Positivity propagation from an ordered coefficient-ratio test -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem ordered_sign_pos_above (S : Finset ℕ) (a : ℕ → ℝ) (s : ℕ)
    (hS : ∀ i ∈ S, i ≤ s)
    (horder : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → 0 ≤ a j → 0 ≤ a i)
    {c x : ℝ} (hc : 0 < c) (hcx : c ≤ x)
    (hpos : 0 < ∑ i ∈ S, a i * c ^ (s - i)) :
    0 < ∑ i ∈ S, a i * x ^ (s - i) := by
  classical
  let P := S.filter (fun i => 0 ≤ a i)
  have hP : P.Nonempty := by
    by_contra hn
    have hnone : ∀ i ∈ S, a i ≤ 0 := by
      intro i hi
      by_contra ha
      have hle : 0 ≤ a i := (lt_of_not_ge ha).le
      exact hn ⟨i, Finset.mem_filter.mpr ⟨hi, hle⟩⟩
    have hsum : (∑ i ∈ S, a i * c ^ (s - i)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact mul_nonpos_of_nonpos_of_nonneg (hnone i hi) (pow_nonneg hc.le _)
    linarith
  let m := P.max' hP
  have hmP : m ∈ P := Finset.max'_mem P hP
  have hmS : m ∈ S := (Finset.mem_filter.mp hmP).1
  have hm0 : 0 ≤ a m := (Finset.mem_filter.mp hmP).2
  have hms : m ≤ s := hS m hmS
  apply oneSignChange_pos_above S a (fun i => s - i) (s - m) hc hcx
  · intro i hi he
    have his : i ≤ s := hS i hi
    have hmi : m < i := by omega
    by_contra hneg
    have hiP : i ∈ P := Finset.mem_filter.mpr ⟨hi, (lt_of_not_ge hneg).le⟩
    have : i ≤ m := Finset.le_max' P i hiP
    omega
  · intro i hi he
    have his : i ≤ s := hS i hi
    exact horder i hi m hmS (by omega) hm0
  · exact hpos

theorem ratio_ordered_sign {I : Type} (S : Finset I)
    (A B : I → ℝ) (hB : ∀ i ∈ S, 0 < B i) {i j : I}
    (hi : i ∈ S) (hj : j ∈ S)
    (hR : A j / B j ≤ A i / B i) (hpos : 0 ≤ A j - B j) :
    0 ≤ A i - B i := by
  have hRj : 1 ≤ A j / B j := (one_le_div (hB j hj)).2 (by linarith)
  have hRi : 1 ≤ A i / B i := hRj.trans hR
  have h := (one_le_div (hB i hi)).mp hRi
  linarith

theorem ratio_pos_above (S : Finset ℕ) (A B : ℕ → ℝ) (s : ℕ)
    (hS : ∀ i ∈ S, i ≤ s) (hB : ∀ i ∈ S, 0 < B i)
    (hR : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → A j / B j ≤ A i / B i)
    {c x : ℝ} (hc : 0 < c) (hcx : c ≤ x)
    (hpos : 0 < ∑ i ∈ S, (A i - B i) * c ^ (s - i)) :
    0 < ∑ i ∈ S, (A i - B i) * x ^ (s - i) := by
  apply ordered_sign_pos_above S (fun i => A i - B i) s hS _ hc hcx hpos
  intro i hi j hj hij hposj
  exact ratio_ordered_sign S A B hB hi hj (hR i hi j hj hij) hposj

end ChromaticSpectral
