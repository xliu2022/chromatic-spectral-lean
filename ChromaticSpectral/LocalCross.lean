module

public import ChromaticSpectral.LocalRatios

/-! # Strict increase of the pure cross layer -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

noncomputable def gapBase (c : ℕ) : ℝ := ((c : ℝ) + 1) / ((c : ℝ) - 1)

noncomputable def gapNewCoeff (c s : ℕ) (θ : ℝ) (u : ℕ) : ℝ :=
  gapA c s u * (gapX c s (s - u)) ^ θ

noncomputable def gapOldCoeff (c s : ℕ) (θ : ℝ) (u : ℕ) : ℝ :=
  gapB c s u * (gapY c u) ^ θ

theorem gapBase_pos {c : ℕ} (hc : 2 ≤ c) : 0 < gapBase c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  exact div_pos (by linarith) (by linarith)

theorem gapBase_one_le {c : ℕ} (hc : 2 ≤ c) : 1 ≤ gapBase c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  exact (one_le_div (by linarith : 0 < (c : ℝ) - 1)).2 (by linarith)

theorem gapBeta_factor {c : ℕ} (hc : 2 ≤ c) :
    gapBeta c = gapQ c * gapQ c * gapBase c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (c : ℝ) ≠ 0 := by linarith
  have hcm : (c : ℝ) - 1 ≠ 0 := by linarith
  unfold gapBeta gapQ gapBase
  field_simp
  ring

theorem gapA_reflect {c s u : ℕ} (hu : u ≤ s) :
    gapA c s (s - u) = gapA c s u := by
  simp only [gapA, Nat.sub_sub_self hu, mul_comm]

theorem gapX_reflect {c s u : ℕ} (hu : u ≤ s) :
    gapX c s (s - u) = gapQ c ^ (s - u) * gapBeta c ^ u := by
  simp only [gapX, Nat.sub_sub_self hu]

theorem gapX_reflect_ratio {c s u : ℕ} (hc : 2 ≤ c) (hu : u ≤ s) :
    gapX c s (s - u) / gapY c u = gapQ c ^ s * gapBase c ^ u := by
  have hq := gapQ_pos hc
  have hpow : gapQ c ^ (s - u) * gapQ c ^ u = gapQ c ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hu]
  apply (div_eq_iff (pow_ne_zero _ hq.ne')).2
  rw [gapX_reflect hu, gapBeta_factor hc, mul_pow, mul_pow]
  calc
    _ = (gapQ c ^ (s - u) * gapQ c ^ u) * gapBase c ^ u * gapQ c ^ u := by ring
    _ = _ := by rw [hpow]

theorem gapCoeff_ratio {c s u : ℕ} (hc : 2 ≤ c) (hu : u ≤ s) (θ : ℝ) :
    gapNewCoeff c s θ u / gapOldCoeff c s θ u =
      (gapQ c ^ s) ^ θ * (gapRatio c s u * (gapBase c ^ θ) ^ u) := by
  have hx := (gapX_pos hc (s := s) (u := s - u)).le
  have hy : 0 ≤ gapY c u := (pow_pos (gapQ_pos hc) u).le
  calc
    _ = gapRatio c s u * (gapX c s (s - u) / gapY c u) ^ θ := by
      rw [Real.div_rpow hx hy]
      unfold gapNewCoeff gapOldCoeff gapRatio
      ring
    _ = _ := by
      rw [gapX_reflect_ratio hc hu,
        Real.mul_rpow (pow_nonneg (gapQ_pos hc).le _) (pow_nonneg (gapBase_pos hc).le _),
        ← Real.rpow_pow_comm (gapBase_pos hc).le θ u]
      ring

theorem gapCoeff_ratio_antitone {c s : ℕ} (hc : 2 ≤ c) (hsc : s ≤ c)
    {θ : ℝ} (hθ1 : θ ≤ 1) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hjs : j ≤ s) :
    gapNewCoeff c s θ j / gapOldCoeff c s θ j ≤
      gapNewCoeff c s θ i / gapOldCoeff c s θ i := by
  rw [gapCoeff_ratio hc hjs, gapCoeff_ratio hc (by omega)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (pow_nonneg (gapQ_pos hc).le _) _)
  apply gapRatio_geometric_antitone hc hsc
  · exact (Real.rpow_pos_of_pos (gapBase_pos hc) _).le
  · simpa only [Real.rpow_one, gapBase] using
      Real.rpow_le_rpow_of_exponent_le (gapBase_one_le hc) hθ1
  · exact hi
  · exact hij
  · exact hjs

theorem gapNewCoeff_sum {c s : ℕ} (θ : ℝ) :
    (∑ u ∈ Finset.Ico 1 s, gapNewCoeff c s θ u) =
      ∑ u ∈ Finset.Ico 1 s, gapA c s u * (gapX c s u) ^ θ := by
  have h := Finset.sum_Ico_reflect
    (fun u => gapA c s u * (gapX c s u) ^ θ) 1 (m := s) (n := s) (by omega)
  simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro u hu
  rw [gapA_reflect (by have := (Finset.mem_Ico.mp hu).2; omega)]
  rfl

theorem gap_cross_normalized_lt {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c)
    {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hz : 1 ≤ z) :
    (∑ u ∈ Finset.Ico 1 s, gapOldCoeff c s θ u * z ^ (s - u)) <
      ∑ u ∈ Finset.Ico 1 s, gapNewCoeff c s θ u * z ^ (s - u) := by
  have hc : 2 ≤ c := by omega
  have hpos : 0 < ∑ u ∈ Finset.Ico 1 s,
      (gapNewCoeff c s θ u - gapOldCoeff c s θ u) * (1 : ℝ) ^ (s - u) := by
    simp only [one_pow, mul_one, Finset.sum_sub_distrib]
    rw [gapNewCoeff_sum]
    exact sub_pos.mpr (gap_boundary_rpow_lt hs hsc hθ hθ1)
  have h := ratio_pos_above (Finset.Ico 1 s) (gapNewCoeff c s θ)
    (gapOldCoeff c s θ) s
    (fun i hi => (Finset.mem_Ico.mp hi).2.le)
    (fun i hi => mul_pos (gapB_pos hsc (Finset.mem_Ico.mp hi).1
      (Finset.mem_Ico.mp hi).2.le)
      (Real.rpow_pos_of_pos (pow_pos (gapQ_pos hc) i) θ))
    (fun i hi j hj hij => gapCoeff_ratio_antitone hc hsc hθ1
      (Finset.mem_Ico.mp hi).1 hij (Finset.mem_Ico.mp hj).2.le)
    (by norm_num : (0 : ℝ) < 1) hz hpos
  simp only [sub_mul, Finset.sum_sub_distrib] at h
  exact sub_pos.mp h

end ChromaticSpectral
