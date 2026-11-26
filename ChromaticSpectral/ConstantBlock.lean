module

public import ChromaticSpectral.WeightedBinomial

/-! # Shrinking a constant class with fixed mass -/

@[expose] public section

namespace ChromaticSpectral

theorem choose_mul_rpow_pow_le {a b s : ℕ} (hb : 0 < b) (hba : b ≤ a)
    {θ : ℝ} (hθ1 : θ ≤ 1) :
    (b.choose s : ℝ) * ((a : ℝ) ^ θ) ^ s ≤
      (a.choose s : ℝ) * ((b : ℝ) ^ θ) ^ s := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le hb hba)
  have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
  have hratio : 1 ≤ (a : ℝ) / b := (one_le_div hbR).2 hbaR
  have hrpow : ((a : ℝ) / b) ^ θ ≤ (a : ℝ) / b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hratio hθ1
  have hpow : (((a : ℝ) / b) ^ θ) ^ s ≤ ((a : ℝ) / b) ^ s :=
    pow_le_pow_left₀ (Real.rpow_nonneg (div_nonneg haR.le hbR.le) _) hrpow s
  have hbin : (b.choose s : ℝ) * ((a : ℝ) / b) ^ s ≤ (a.choose s : ℝ) := by
    rw [div_pow, ← mul_div_assoc]
    exact (div_le_iff₀ (pow_pos hbR s)).2 (choose_mul_pow_le a b s hba)
  have h := (mul_le_mul_of_nonneg_left hpow
    (show (0 : ℝ) ≤ b.choose s by positivity)).trans hbin
  rw [Real.div_rpow haR.le hbR.le, div_pow, ← mul_div_assoc] at h
  exact (div_le_iff₀ (pow_pos (Real.rpow_pos_of_pos hbR θ) s)).mp h

theorem constantBlock_mono {a b s : ℕ} (hb : 0 < b) (hba : b ≤ a)
    {A θ : ℝ} (hA : 0 ≤ A) (hθ1 : θ ≤ 1) :
    (b.choose s : ℝ) * ((A / (b : ℝ)) ^ θ) ^ s ≤
      (a.choose s : ℝ) * ((A / (a : ℝ)) ^ θ) ^ s := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le hb hba)
  rw [Real.div_rpow hA hbR.le, Real.div_rpow hA haR.le, div_pow, div_pow,
    ← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_div_iff₀
    (pow_pos (Real.rpow_pos_of_pos hbR θ) s)
    (pow_pos (Real.rpow_pos_of_pos haR θ) s)).2
  have h := mul_le_mul_of_nonneg_right (choose_mul_rpow_pow_le (s := s) hb hba hθ1)
    (pow_nonneg (Real.rpow_nonneg hA θ) s)
  nlinarith

theorem constantBlock_reduce {c s : ℕ} (hc : 0 < c)
    {A θ : ℝ} (hA : 0 ≤ A) (hθ1 : θ ≤ 1) :
    (c.choose s : ℝ) * ((A / (c : ℝ)) ^ θ) ^ s ≤
      ((c + 1).choose s : ℝ) * ((A / ((c : ℝ) + 1)) ^ θ) ^ s := by
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    constantBlock_mono (s := s) hc (Nat.le_succ c) hA hθ1

end ChromaticSpectral
