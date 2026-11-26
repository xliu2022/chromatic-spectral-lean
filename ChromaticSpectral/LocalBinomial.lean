module

public import ChromaticSpectral.TruncatedMoments
public import ChromaticSpectral.OneSignChange

/-! # Binomial identities for the two-class balancing move -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

def gapA (c s i : ℕ) : ℝ := (c.choose i : ℝ) * (c.choose (s - i) : ℝ)

def gapB (c s i : ℕ) : ℝ := ((c + 1).choose i : ℝ) * ((c - 1).choose (s - i) : ℝ)

def gapD (c s i : ℕ) : ℝ :=
  (c.choose i : ℝ) * ((c - 1).choose (s - i - 1) : ℝ) -
    ((c - 1).choose (s - 1) : ℝ)

theorem gapA_nonneg (c s i : ℕ) : 0 ≤ gapA c s i := by
  unfold gapA
  positivity

theorem gapB_nonneg (c s i : ℕ) : 0 ≤ gapB c s i := by
  unfold gapB
  positivity

theorem gapA_pos {c s i : ℕ} (hsc : s ≤ c) (hi : i ≤ s) : 0 < gapA c s i := by
  exact mul_pos (by exact_mod_cast Nat.choose_pos (le_trans hi hsc))
    (by exact_mod_cast Nat.choose_pos (show s - i ≤ c by omega))

theorem gapB_pos {c s i : ℕ} (hsc : s ≤ c) (hi : 1 ≤ i) (his : i ≤ s) :
    0 < gapB c s i := by
  exact mul_pos (by exact_mod_cast Nat.choose_pos (show i ≤ c + 1 by omega))
    (by exact_mod_cast Nat.choose_pos (show s - i ≤ c - 1 by omega))

@[simp] theorem gapD_zero (c s : ℕ) : gapD c s 0 = 0 := by
  simp [gapD]

theorem gap_difference {c s i : ℕ} (hc : 0 < c) (hi : 0 < i) (his : i < s) :
    gapA c s i - gapB c s i = gapD c s i - gapD c s (i - 1) := by
  have hchoose1 : (c.choose (s - i) : ℝ) =
      ((c - 1).choose (s - i - 1) : ℝ) + ((c - 1).choose (s - i) : ℝ) := by
    exact_mod_cast Nat.choose_eq_choose_pred_add hc (by omega : 0 < s - i)
  have hchoose2 : ((c + 1).choose i : ℝ) =
      (c.choose (i - 1) : ℝ) + (c.choose i : ℝ) := by
    exact_mod_cast Nat.choose_succ_left c i hi
  have hsub : s - (i - 1) - 1 = s - i := by omega
  unfold gapA gapB gapD
  rw [hchoose1, hchoose2, hsub]
  ring

theorem gap_partial_sum {c s : ℕ} (hc : 0 < c) {i : ℕ} (hi : i < s) :
    (∑ u ∈ Finset.range i, (gapA c s (u + 1) - gapB c s (u + 1))) =
      gapD c s i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, ih (by omega), gap_difference hc (by omega) hi]
    simp

theorem gapD_formula {c s i : ℕ} (hc : 0 < c) (his : i < s) :
    gapD c s i = ((s - i : ℕ) : ℝ) / (c : ℝ) * gapA c s i -
      ((c - 1).choose (s - 1) : ℝ) := by
  have hcR : (c : ℝ) ≠ 0 := by positivity
  have hmul : (c : ℝ) * ((c - 1).choose (s - i - 1) : ℝ) =
      (c.choose (s - i) : ℝ) * ((s - i : ℕ) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (c - 1) (s - i - 1)
    have hc' : c - 1 + 1 = c := by omega
    have hs' : s - i - 1 + 1 = s - i := by omega
    rw [hc', hs'] at h
    exact_mod_cast h
  unfold gapD gapA
  field_simp
  nlinarith [congrArg (fun z : ℝ => (c.choose i : ℝ) * z) hmul]

theorem gapD_last {c s : ℕ} (hc : 0 < c) (hs : 2 ≤ s) :
    gapD c s (s - 1) = ((c - 1).choose (s - 2) : ℝ) := by
  have hsub : s - (s - 1) - 1 = 0 := by omega
  have hchoose : (c.choose (s - 1) : ℝ) =
      ((c - 1).choose (s - 2) : ℝ) + ((c - 1).choose (s - 1) : ℝ) := by
    have h := Nat.choose_eq_choose_pred_add hc (by omega : 0 < s - 1)
    simpa [Nat.sub_sub] using congrArg (fun z : ℕ => (z : ℝ)) h
  simp only [gapD, hsub, Nat.choose_zero_right, Nat.cast_one, mul_one]
  linarith

theorem gapA_last {c s : ℕ} (hc : 0 < c) (hs : 2 ≤ s) :
    gapA c s (s - 1) / (c : ℝ) ^ 2 =
      ((c - 1).choose (s - 2) : ℝ) / (s - 1 : ℕ) := by
  have hcR : (c : ℝ) ≠ 0 := by positivity
  have hsR : ((s - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : s - 1 ≠ 0)
  have hmul : (c : ℝ) * ((c - 1).choose (s - 2) : ℝ) =
      (c.choose (s - 1) : ℝ) * ((s - 1 : ℕ) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (c - 1) (s - 2)
    have hc' : c - 1 + 1 = c := by omega
    have hs' : s - 2 + 1 = s - 1 := by omega
    rw [hc', hs'] at h
    exact_mod_cast h
  have hsub : s - (s - 1) = 1 := by omega
  simp only [gapA, hsub, Nat.choose_one_right]
  field_simp
  nlinarith [congrArg (fun z : ℝ => (c : ℝ) * z) hmul]

theorem gapK_formula {c s : ℕ} (hsc : s ≤ c) (hs : 2 ≤ s) :
    ((c - 1).choose (s - 1) : ℝ) =
      ((c : ℝ) - s + 1) / ((s : ℝ) - 1) * ((c - 1).choose (s - 2) : ℝ) := by
  have hsR : (s : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have h := Nat.choose_succ_right_eq (c - 1) (s - 2)
  have hs' : s - 2 + 1 = s - 1 := by omega
  rw [hs'] at h
  have hreal := congrArg (fun z : ℕ => (z : ℝ)) h
  push_cast at hreal
  have hsub : ((c - 1 - (s - 2) : ℕ) : ℝ) = (c : ℝ) - s + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
    ring
  rw [hsub, Nat.cast_sub (by omega)] at hreal
  norm_num at hreal
  field_simp
  nlinarith

end ChromaticSpectral
