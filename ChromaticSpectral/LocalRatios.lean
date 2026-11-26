module

public import ChromaticSpectral.LocalBoundary
public import ChromaticSpectral.OrderedSign

/-! # Ordered coefficient ratios for the two-class move -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

noncomputable def gapRatio (c s i : ℕ) : ℝ := gapA c s i / gapB c s i

theorem gapRatio_pos {c s i : ℕ} (hsc : s ≤ c) (hi : 1 ≤ i) (his : i ≤ s) :
    0 < gapRatio c s i :=
  div_pos (gapA_pos hsc his) (gapB_pos hsc hi his)

theorem gapRatio_formula {c s i : ℕ} (hsc : s ≤ c)
    (hi : 1 ≤ i) (his : i ≤ s) :
    gapRatio c s i = ((c : ℝ) + 1 - i) * c /
      (((c : ℝ) + 1) * ((c : ℝ) - s + i)) := by
  have hc : 0 < c := by omega
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hscR : (s : ℝ) ≤ c := by exact_mod_cast hsc
  have hB := gapB_pos hsc hi his
  have hden : 0 < ((c : ℝ) + 1) * ((c : ℝ) - s + i) :=
    mul_pos (by positivity) (by linarith)
  have h1 : (c.choose i : ℝ) * ((c : ℝ) + 1) =
      ((c + 1).choose i : ℝ) * ((c : ℝ) + 1 - i) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_mul_succ_eq c i)
    push_cast at h
    rw [Nat.cast_sub (by omega)] at h
    push_cast at h
    exact h
  have h2 : ((c - 1).choose (s - i) : ℝ) * c =
      (c.choose (s - i) : ℝ) * ((c : ℝ) - s + i) := by
    have h := Nat.choose_mul_succ_eq (c - 1) (s - i)
    rw [show c - 1 + 1 = c by omega] at h
    have hR := congrArg (fun z : ℕ => (z : ℝ)) h
    push_cast at hR
    rw [Nat.cast_sub (by omega), Nat.cast_sub his] at hR
    convert hR using 1
    ring
  apply (div_eq_div_iff hB.ne' hden.ne').2
  unfold gapA gapB
  calc
    _ = ((c.choose i : ℝ) * ((c : ℝ) + 1)) *
        ((c.choose (s - i) : ℝ) * ((c : ℝ) - s + i)) := by ring
    _ = _ := by rw [h1, ← h2]; ring

theorem gapRatio_succ {c s i : ℕ} (hsc : s ≤ c)
    (hi : 1 ≤ i) (his : i + 1 ≤ s) :
    gapRatio c s (i + 1) = gapRatio c s i *
      (((c : ℝ) - i) / ((c : ℝ) + 1 - i)) *
      (((c : ℝ) - s + i) / ((c : ℝ) - s + i + 1)) := by
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hisR : (i : ℝ) + 1 ≤ s := by exact_mod_cast his
  have hscR : (s : ℝ) ≤ c := by exact_mod_cast hsc
  have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
  have ha : (c : ℝ) + 1 - i ≠ 0 := by linarith
  have hb : (c : ℝ) - s + i ≠ 0 := by linarith
  have hb1 : (c : ℝ) - s + i + 1 ≠ 0 := by linarith
  have hb1' : (c : ℝ) - s + ((i : ℝ) + 1) ≠ 0 := by linarith
  rw [gapRatio_formula hsc (by omega) his,
    gapRatio_formula hsc hi (by omega)]
  push_cast
  field_simp [hb1']
  ring

theorem gapRatio_succ_mul_le {c s i : ℕ} (hc : 2 ≤ c) (hsc : s ≤ c)
    (hi : 1 ≤ i) (his : i + 1 ≤ s) :
    gapRatio c s (i + 1) * (((c : ℝ) + 1) / ((c : ℝ) - 1)) ≤
      gapRatio c s i := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hisR : (i : ℝ) + 1 ≤ s := by exact_mod_cast his
  have hscR : (s : ℝ) ≤ c := by exact_mod_cast hsc
  have hc0 : (0 : ℝ) < c := by linarith
  have hc1 : 0 < (c : ℝ) + 1 := by linarith
  have hcm : 0 < (c : ℝ) - 1 := by linarith
  have ha : 0 < (c : ℝ) + 1 - i := by linarith
  have hb : 0 ≤ (c : ℝ) - s + i := by linarith
  have hb1 : 0 < (c : ℝ) - s + i + 1 := by linarith
  have hfirst : ((c : ℝ) - i) / ((c : ℝ) + 1 - i) ≤
      (c : ℝ) / ((c : ℝ) + 1) := by
    apply (div_le_div_iff₀ ha hc1).2
    nlinarith
  have hsecond : ((c : ℝ) - s + i) / ((c : ℝ) - s + i + 1) ≤
      ((c : ℝ) - 1) / (c : ℝ) := by
    apply (div_le_div_iff₀ hb1 hc0).2
    nlinarith
  have hprod := mul_le_mul hfirst hsecond (div_nonneg hb hb1.le)
    (div_nonneg hc0.le hc1.le)
  have hbound :
      (((c : ℝ) - i) / ((c : ℝ) + 1 - i)) *
        (((c : ℝ) - s + i) / ((c : ℝ) - s + i + 1)) *
          (((c : ℝ) + 1) / ((c : ℝ) - 1)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hprod (div_nonneg hc1.le hcm.le)
    have heq : (c : ℝ) / ((c : ℝ) + 1) * (((c : ℝ) - 1) / c) *
        (((c : ℝ) + 1) / ((c : ℝ) - 1)) = 1 := by field_simp
    exact h.trans_eq heq
  rw [gapRatio_succ hsc hi his]
  have h := mul_le_mul_of_nonneg_left hbound (gapRatio_pos hsc hi (by omega)).le
  nlinarith

theorem gapRatio_geometric_antitone {c s : ℕ} (hc : 2 ≤ c) (hsc : s ≤ c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ ((c : ℝ) + 1) / ((c : ℝ) - 1))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjs : j ≤ s) :
    gapRatio c s j * t ^ j ≤ gapRatio c s i * t ^ i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ k hik ih =>
    have hks : k ≤ s := by omega
    have hstep : gapRatio c s (k + 1) * t ≤ gapRatio c s k := by
      exact (mul_le_mul_of_nonneg_left ht
        (gapRatio_pos hsc (by omega) hjs).le).trans
          (gapRatio_succ_mul_le hc hsc (by omega) hjs)
    have hpow := mul_le_mul_of_nonneg_right hstep (pow_nonneg ht0 k)
    rw [pow_succ]
    have hstep' : gapRatio c s (k + 1) * (t ^ k * t) ≤ gapRatio c s k * t ^ k := by
      nlinarith
    exact hstep'.trans (ih hks)

end ChromaticSpectral
