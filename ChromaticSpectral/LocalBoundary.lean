module

public import ChromaticSpectral.LocalBalancing

/-! # Strict boundary certificate for every real power in (0,1] -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem gap_certificate_pos {c s j : ℕ}
    (hs : 3 ≤ s) (hsc : s ≤ c) (hj : 1 ≤ j) (hjs : j < s) :
    0 < ((c - 1).choose (s - 2) : ℝ) / ((s : ℝ) - 1) *
      (((c : ℝ) - 1) * gapQ c ^ (s - 1) -
        ((c : ℝ) - s + 1) * gapQ c ^ j) := by
  have hc : 3 ≤ c := le_trans hs hsc
  have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hcpos : (0 : ℝ) < c := by linarith
  have hcne : (c : ℝ) ≠ 0 := hcpos.ne'
  have hq : 0 < gapQ c := gapQ_pos (by omega)
  let M := s - 1 - j
  have hM : M ≤ s - 2 := by dsimp [M]; omega
  have hMR : (M : ℝ) ≤ (s : ℝ) - 2 := by
    have h : (M : ℝ) ≤ ((s - 2 : ℕ) : ℝ) := by exact_mod_cast hM
    have hs2 : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    exact h.trans_eq hs2
  have hdiv1 : 1 / (c : ℝ) ≤ 1 := (div_le_one hcpos).2 (by linarith)
  have hB := one_add_mul_le_pow (by linarith : -(2 : ℝ) ≤ -(1 / (c : ℝ))) M
  have hBern : 1 - (M : ℝ) / (c : ℝ) ≤ gapQ c ^ M := by
    simpa [gapQ, sub_eq_add_neg, div_eq_mul_inv, mul_neg] using hB
  have hBweak : 1 - ((s : ℝ) - 2) / (c : ℝ) ≤ gapQ c ^ M := by
    have hdiv := div_le_div_of_nonneg_right hMR hcpos.le
    linarith
  have hcalc : ((c : ℝ) - 1) * (1 - ((s : ℝ) - 2) / (c : ℝ)) -
      ((c : ℝ) - s + 1) = ((s : ℝ) - 2) / (c : ℝ) := by
    field_simp
    ring
  have hprod := mul_le_mul_of_nonneg_left hBweak (by linarith : 0 ≤ (c : ℝ) - 1)
  have hbracket : 0 < ((c : ℝ) - 1) * gapQ c ^ M - ((c : ℝ) - s + 1) := by
    have hpos : 0 < ((s : ℝ) - 2) / (c : ℝ) := div_pos (by linarith) hcpos
    linarith
  have hpow : gapQ c ^ (s - 1) = gapQ c ^ j * gapQ c ^ M := by
    rw [← pow_add]
    congr 1
    dsimp [M]
    omega
  have hmain : 0 < ((c : ℝ) - 1) * gapQ c ^ (s - 1) -
      ((c : ℝ) - s + 1) * gapQ c ^ j := by
    rw [hpow]
    have h := mul_pos (pow_pos hq j) hbracket
    nlinarith
  apply mul_pos _ hmain
  apply div_pos
  · exact_mod_cast Nat.choose_pos (show s - 2 ≤ c - 1 by omega)
  · linarith

theorem gap_boundary_moment_pos {c s j : ℕ}
    (hs : 3 ≤ s) (hsc : s ≤ c) (hj : 1 ≤ j) (hjs : j < s) :
    0 < truncatedMoment (Finset.Ico 1 s) (gapA c s) (gapX c s) (gapY c j) -
      truncatedMoment (Finset.Ico 1 s) (gapB c s) (gapY c) (gapY c j) := by
  have hc : 3 ≤ c := le_trans hs hsc
  rw [gap_boundary_moment_formula hc hsc hj hjs]
  have hL := gap_loss_bound (s := s) (j := j) hc
  have hI := gap_certificate_identity hc hs hsc hj hjs
  have hP := gap_certificate_pos hs hsc hj hjs
  linarith

theorem gap_boundary_moment_le {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c) :
    ∀ T, 0 ≤ T →
      truncatedMoment (Finset.Ico 1 s) (gapB c s) (gapY c) T ≤
        truncatedMoment (Finset.Ico 1 s) (gapA c s) (gapX c s) T := by
  have hc : 2 ≤ c := by omega
  apply truncatedMoment_le_of_support_checks
  · intro u hu
    exact gapA_nonneg c s u
  · intro u hu
    exact (gapX_pos hc).le
  · intro u hu
    exact (pow_pos (gapQ_pos hc) u).le
  · intro j hj
    exact (sub_pos.mp (gap_boundary_moment_pos hs hsc
      (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)).le

theorem gap_boundary_total_lt {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c) :
    (∑ u ∈ Finset.Ico 1 s, gapB c s u * gapY c u) <
      ∑ u ∈ Finset.Ico 1 s, gapA c s u * gapX c s u := by
  have hc : 2 ≤ c := by omega
  have hq := gapQ_pos hc
  have hq1 := (gapQ_lt_one (show 0 < c by omega)).le
  have hY : truncatedMoment (Finset.Ico 1 s) (gapB c s) (gapY c) (gapY c 1) =
      ∑ u ∈ Finset.Ico 1 s, gapB c s u * gapY c u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [min_eq_right]
    exact pow_le_pow_of_le_one hq.le hq1 (Finset.mem_Ico.mp hu).1
  have hX : truncatedMoment (Finset.Ico 1 s) (gapA c s) (gapX c s) (gapY c 1) =
      ∑ u ∈ Finset.Ico 1 s, gapA c s u * gapX c s u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [min_eq_right]
    exact (gapX_le_Y hc).trans
      (pow_le_pow_of_le_one hq.le hq1 (Finset.mem_Ico.mp hu).1)
  have h := gap_boundary_moment_pos hs hsc (j := 1) le_rfl (by omega)
  rw [hY, hX] at h
  exact sub_pos.mp h

theorem gap_boundary_rpow_lt {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∑ u ∈ Finset.Ico 1 s, gapB c s u * (gapY c u) ^ θ) <
      ∑ u ∈ Finset.Ico 1 s, gapA c s u * (gapX c s u) ^ θ := by
  have hc : 2 ≤ c := by omega
  apply rpow_sum_lt_of_truncatedMoment_le
  · intro u hu
    exact (gapX_pos hc).le
  · intro u hu
    exact (pow_pos (gapQ_pos hc) u).le
  · exact hθ
  · exact hθ1
  · exact gap_boundary_moment_le hs hsc
  · exact gap_boundary_total_lt hs hsc

end ChromaticSpectral
