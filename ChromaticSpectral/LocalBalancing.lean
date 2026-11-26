module

public import ChromaticSpectral.LocalBinomial
public import ChromaticSpectral.TruncatedSupport

/-!
# The local cross-layer inequality

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.

The finite certificates below use the normalized support values
`q^u * beta^(s-u)` and `q^u`. This removes a common positive scale
from the boundary calculation in Lemma 4.8.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

noncomputable def gapQ (c : ℕ) : ℝ := 1 - 1 / (c : ℝ)
noncomputable def gapBeta (c : ℕ) : ℝ := 1 - 1 / (c : ℝ) ^ 2
noncomputable def gapX (c s u : ℕ) : ℝ := gapQ c ^ u * gapBeta c ^ (s - u)
noncomputable def gapY (c u : ℕ) : ℝ := gapQ c ^ u

theorem gapQ_pos {c : ℕ} (hc : 2 ≤ c) : 0 < gapQ c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hdiv : 1 / (c : ℝ) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  unfold gapQ
  linarith

theorem gapQ_lt_one {c : ℕ} (hc : 0 < c) : gapQ c < 1 := by
  unfold gapQ
  have : (0 : ℝ) < c := by exact_mod_cast hc
  have := one_div_pos.mpr this
  linarith

theorem gapBeta_pos {c : ℕ} (hc : 2 ≤ c) : 0 < gapBeta c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hdiv : 1 / (c : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
  unfold gapBeta
  linarith

theorem gapBeta_lt_one {c : ℕ} (hc : 0 < c) : gapBeta c < 1 := by
  unfold gapBeta
  have : (0 : ℝ) < c := by exact_mod_cast hc
  have hpos : 0 < 1 / (c : ℝ) ^ 2 := by positivity
  linarith

theorem gapBeta_pow_lower {c : ℕ} (hc : 2 ≤ c) (u : ℕ) :
    1 - (u : ℝ) / (c : ℝ) ^ 2 ≤ gapBeta c ^ u := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hdiv : 1 / (c : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
  have h := one_add_mul_le_pow (by linarith : -(2 : ℝ) ≤ -(1 / (c : ℝ) ^ 2)) u
  simpa [gapBeta, sub_eq_add_neg, div_eq_mul_inv, mul_neg] using h

theorem gapBeta_pow_gt_q {c u : ℕ} (hc : 2 ≤ c) (hu : u < c) :
    gapQ c < gapBeta c ^ u := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have huR : (u : ℝ) < c := by exact_mod_cast hu
  have hdiv : (u : ℝ) / (c : ℝ) ^ 2 < 1 / (c : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) (by linarith)).2
    nlinarith
  have hbound : gapQ c < 1 - (u : ℝ) / (c : ℝ) ^ 2 := by
    unfold gapQ
    linarith
  exact hbound.trans_le (gapBeta_pow_lower hc u)

theorem gapX_pos {c s u : ℕ} (hc : 2 ≤ c) : 0 < gapX c s u := by
  exact mul_pos (pow_pos (gapQ_pos hc) _) (pow_pos (gapBeta_pos hc) _)

theorem gapX_le_Y {c s u : ℕ} (hc : 2 ≤ c) : gapX c s u ≤ gapY c u := by
  have hb : gapBeta c ^ (s - u) ≤ 1 :=
    pow_le_one₀ (gapBeta_pos hc).le (gapBeta_lt_one (by omega)).le
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (gapQ_pos hc).le _)).trans_eq (mul_one _)

theorem gap_min_X {c s u j : ℕ} (hc : 3 ≤ c) (hsc : s ≤ c)
    (hu : 1 ≤ u) (hus : u < s) (_hj : 1 ≤ j) (_hjs : j < s) :
    min (gapY c j) (gapX c s u) =
      if u < j then gapY c j else gapX c s u := by
  have hq := gapQ_pos (show 2 ≤ c by omega)
  have hq1 := (gapQ_lt_one (show 0 < c by omega)).le
  by_cases huj : u < j
  · rw [ite_eq_left huj, min_eq_left]
    have hpow : gapQ c ^ j ≤ gapQ c ^ (u + 1) :=
      pow_le_pow_of_le_one hq.le hq1 (by omega)
    have hb := gapBeta_pow_gt_q (show 2 ≤ c by omega) (show s - u < c by omega)
    have hh := mul_lt_mul_of_pos_left hb (pow_pos hq u)
    exact hpow.trans (by simpa [gapY, gapX, pow_succ] using hh.le)
  · rw [ite_eq_right huj, min_eq_right]
    exact (gapX_le_Y (show 2 ≤ c by omega)).trans
      (pow_le_pow_of_le_one hq.le hq1 (Nat.le_of_not_gt huj))

theorem gap_min_Y {c u j : ℕ} (hc : 2 ≤ c) :
    min (gapY c j) (gapY c u) = if u < j then gapY c j else gapY c u := by
  have hq := gapQ_pos hc
  have hq1 := (gapQ_lt_one (show 0 < c by omega)).le
  by_cases huj : u < j
  · rw [ite_eq_left huj, min_eq_left]
    exact pow_le_pow_of_le_one hq.le hq1 huj.le
  · rw [ite_eq_right huj, min_eq_right]
    exact pow_le_pow_of_le_one hq.le hq1 (Nat.le_of_not_gt huj)

theorem weighted_differences (D : ℕ → ℝ) (q : ℝ) {j s : ℕ}
    (hj : 0 < j) (hjs : j < s) :
    (∑ u ∈ Finset.Ico j s, q ^ u * (D u - D (u - 1))) =
      q ^ (s - 1) * D (s - 1) - q ^ j * D (j - 1) +
        (1 - q) * ∑ u ∈ Finset.Ico j (s - 1), q ^ u * D u := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hjs' : j < s
    · have hs : 0 < s := by omega
      have hs1 : s - 1 + 1 = s := by omega
      rw [Finset.sum_Ico_succ_top (Nat.le_of_lt hjs'), ih hjs']
      simp only [Nat.add_sub_cancel]
      rw [show (∑ u ∈ Finset.Ico j s, q ^ u * D u) =
          (∑ u ∈ Finset.Ico j (s - 1), q ^ u * D u) + q ^ (s - 1) * D (s - 1) by
            simpa only [hs1] using
              Finset.sum_Ico_succ_top (show j ≤ s - 1 by omega) (fun u => q ^ u * D u)]
      have hpows : q ^ s = q ^ (s - 1) * q := by
        simpa only [hs1] using pow_succ q (s - 1)
      rw [hpows]
      ring
    · have hsj : s = j := by omega
      simp [hsj, mul_sub]

theorem gap_partial_sum_Ico {c s j : ℕ} (hc : 0 < c) (hj : 1 ≤ j) (hjs : j ≤ s) :
    (∑ u ∈ Finset.Ico 1 j, (gapA c s u - gapB c s u)) = gapD c s (j - 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_comm] using gap_partial_sum hc (show j - 1 < s by omega)

theorem gap_boundary_moment_formula {c s j : ℕ}
    (hc : 3 ≤ c) (hsc : s ≤ c) (hj : 1 ≤ j) (hjs : j < s) :
    truncatedMoment (Finset.Ico 1 s) (gapA c s) (gapX c s) (gapY c j) -
      truncatedMoment (Finset.Ico 1 s) (gapB c s) (gapY c) (gapY c j) =
    gapQ c ^ (s - 1) * gapD c s (s - 1) +
      (1 - gapQ c) * ∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u * gapD c s u -
      ∑ u ∈ Finset.Ico j s,
        gapQ c ^ u * gapA c s u * (1 - gapBeta c ^ (s - u)) := by
  let F := fun u => gapA c s u * min (gapY c j) (gapX c s u) -
    gapB c s u * min (gapY c j) (gapY c u)
  have hlow : (∑ u ∈ Finset.Ico 1 j, F u) =
      gapQ c ^ j * gapD c s (j - 1) := by
    calc
      _ = gapQ c ^ j * ∑ u ∈ Finset.Ico 1 j, (gapA c s u - gapB c s u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        obtain ⟨hu0, huj⟩ := Finset.mem_Ico.mp hu
        dsimp [F]
        rw [gap_min_X hc hsc hu0 (by omega) hj hjs,
          gap_min_Y (show 2 ≤ c by omega), ite_eq_left huj]
        simp only [ite_eq_left huj]
        unfold gapY
        ring
      _ = _ := by rw [gap_partial_sum_Ico (by omega) hj hjs.le]
  have hhigh : (∑ u ∈ Finset.Ico j s, F u) =
      (∑ u ∈ Finset.Ico j s, gapQ c ^ u * (gapD c s u - gapD c s (u - 1))) -
      ∑ u ∈ Finset.Ico j s, gapQ c ^ u * gapA c s u *
        (1 - gapBeta c ^ (s - u)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    obtain ⟨hju, hus⟩ := Finset.mem_Ico.mp hu
    dsimp [F]
    rw [gap_min_X hc hsc (by omega) hus hj hjs,
      gap_min_Y (show 2 ≤ c by omega), ite_eq_right (by omega : ¬ u < j)]
    simp only [ite_eq_right (by omega : ¬ u < j)]
    rw [← gap_difference (by omega) (by omega) hus]
    unfold gapX gapY
    ring
  change (∑ u ∈ Finset.Ico 1 s, gapA c s u * min (gapY c j) (gapX c s u)) -
      (∑ u ∈ Finset.Ico 1 s, gapB c s u * min (gapY c j) (gapY c u)) = _
  rw [← Finset.sum_sub_distrib]
  change (∑ u ∈ Finset.Ico 1 s, F u) = _
  rw [← Finset.sum_Ico_consecutive F hj hjs.le, hlow, hhigh,
    weighted_differences (gapD c s) (gapQ c) (by omega) hjs]
  ring

theorem gap_loss_bound {c s j : ℕ} (hc : 3 ≤ c) :
    (∑ u ∈ Finset.Ico j s, gapQ c ^ u * gapA c s u *
      (1 - gapBeta c ^ (s - u))) ≤
    ∑ u ∈ Finset.Ico j s, gapQ c ^ u * gapA c s u *
      ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2 := by
  apply Finset.sum_le_sum
  intro u hu
  have hb := gapBeta_pow_lower (show 2 ≤ c by omega) (s - u)
  have hweight : 0 ≤ gapQ c ^ u * gapA c s u :=
    mul_nonneg (pow_nonneg (gapQ_pos (show 2 ≤ c by omega)).le _) (gapA_nonneg _ _ _)
  have hh := mul_le_mul_of_nonneg_left (by linarith :
    1 - gapBeta c ^ (s - u) ≤ ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2) hweight
  simpa only [mul_div_assoc] using hh

theorem gap_internal_cancellation {c s u : ℕ} (hc : 0 < c) (hus : u < s) :
    (1 - gapQ c) * (gapQ c ^ u * gapD c s u) -
      gapQ c ^ u * gapA c s u * ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2 =
    -(((c - 1).choose (s - 1) : ℝ) / (c : ℝ)) * gapQ c ^ u := by
  have hcR : (c : ℝ) ≠ 0 := by positivity
  rw [gapD_formula hc hus]
  unfold gapQ
  field_simp
  ring

theorem gap_certificate_identity {c s j : ℕ} (hc : 3 ≤ c)
    (hs : 3 ≤ s) (hsc : s ≤ c) (hj : 1 ≤ j) (hjs : j < s) :
    gapQ c ^ (s - 1) * gapD c s (s - 1) +
      (1 - gapQ c) * (∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u * gapD c s u) -
      (∑ u ∈ Finset.Ico j s,
        gapQ c ^ u * gapA c s u * ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2) =
    ((c - 1).choose (s - 2) : ℝ) / ((s : ℝ) - 1) *
      ((c - 1 : ℝ) * gapQ c ^ (s - 1) - ((c : ℝ) - s + 1) * gapQ c ^ j) := by
  have hc0 : 0 < c := by omega
  have hs2 : 2 ≤ s := by omega
  have hcR : (c : ℝ) ≠ 0 := by positivity
  have hsR : (s : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hlast : s - 1 + 1 = s := by omega
  have hsub : s - (s - 1) = 1 := by omega
  have hsplit := Finset.sum_Ico_succ_top (show j ≤ s - 1 by omega)
    (fun u => gapQ c ^ u * gapA c s u * ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2)
  rw [hlast] at hsplit
  rw [hsplit, hsub, Nat.cast_one, mul_one]
  have hcancel :
      (1 - gapQ c) * (∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u * gapD c s u) -
      (∑ u ∈ Finset.Ico j (s - 1),
        gapQ c ^ u * gapA c s u * ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2) =
      -(((c - 1).choose (s - 1) : ℝ) / (c : ℝ)) *
        ∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    exact gap_internal_cancellation hc0 (by have := (Finset.mem_Ico.mp hu).2; omega)
  have hgeom : (1 / (c : ℝ)) * (∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u) =
      gapQ c ^ j - gapQ c ^ (s - 1) := by
    have h := geom_sum_Ico_mul_neg (gapQ c) (show j ≤ s - 1 by omega)
    simpa only [gapQ, sub_sub_cancel, mul_comm] using h
  have hA := gapA_last hc0 hs2
  have hD := gapD_last hc0 hs2
  have hK := gapK_formula hsc hs2
  have hsnat : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hsnat] at hA
  have hcg :
      (1 - gapQ c) * (∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u * gapD c s u) -
      (∑ u ∈ Finset.Ico j (s - 1),
        gapQ c ^ u * gapA c s u * ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2) =
      -((c - 1).choose (s - 1) : ℝ) *
        (gapQ c ^ j - gapQ c ^ (s - 1)) := by
    rw [hcancel, ← hgeom]
    ring
  calc
    _ = gapQ c ^ (s - 1) * gapD c s (s - 1) +
        ((1 - gapQ c) *
          (∑ u ∈ Finset.Ico j (s - 1), gapQ c ^ u * gapD c s u) -
          (∑ u ∈ Finset.Ico j (s - 1),
            gapQ c ^ u * gapA c s u * ((s - u : ℕ) : ℝ) / (c : ℝ) ^ 2)) -
        gapQ c ^ (s - 1) * (gapA c s (s - 1) / (c : ℝ) ^ 2) := by ring
    _ = gapQ c ^ (s - 1) * gapD c s (s - 1) -
        ((c - 1).choose (s - 1) : ℝ) *
          (gapQ c ^ j - gapQ c ^ (s - 1)) -
        gapQ c ^ (s - 1) * (gapA c s (s - 1) / (c : ℝ) ^ 2) := by
      rw [hcg]
      ring
    _ = _ := by
      rw [hD, hK, hA]
      field_simp
      ring

end ChromaticSpectral
