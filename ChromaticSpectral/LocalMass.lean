module

public import ChromaticSpectral.LocalCross

/-! # The cross-layer inequality in class-mass coordinates -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

noncomputable def crossLayer (a b s : ℕ) (x y : ℝ) : ℝ :=
  ∑ u ∈ Finset.Ico 1 s, (a.choose u : ℝ) * (b.choose (s - u) : ℝ) *
    x ^ u * y ^ (s - u)

theorem crossLayer_scale (a b s : ℕ) (K x y : ℝ) :
    crossLayer a b s (K * x) (K * y) = K ^ s * crossLayer a b s x y := by
  unfold crossLayer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hus : u ≤ s := (Finset.mem_Ico.mp hu).2.le
  have hpow : K ^ u * K ^ (s - u) = K ^ s := by
    rw [← pow_add, Nat.add_sub_cancel' hus]
  rw [mul_pow, mul_pow]
  calc
    _ = (K ^ u * K ^ (s - u)) *
        ((a.choose u : ℝ) * (b.choose (s - u) : ℝ) * x ^ u * y ^ (s - u)) := by ring
    _ = _ := by rw [hpow]

theorem crossLayer_gap_old {c s : ℕ} (hc : 2 ≤ c) (θ r : ℝ) :
    crossLayer (c + 1) (c - 1) s (gapQ c ^ θ) (r ^ θ) =
      ∑ u ∈ Finset.Ico 1 s, gapOldCoeff c s θ u * (r ^ θ) ^ (s - u) := by
  apply Finset.sum_congr rfl
  intro u hu
  unfold gapOldCoeff gapB gapY
  rw [Real.rpow_pow_comm (gapQ_pos hc).le]

theorem crossLayer_gap_new {c s : ℕ} (hc : 2 ≤ c) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    crossLayer c c s (gapBeta c ^ θ) ((gapQ c * r) ^ θ) =
      ∑ u ∈ Finset.Ico 1 s, gapNewCoeff c s θ u * (r ^ θ) ^ (s - u) := by
  apply Finset.sum_congr rfl
  intro u hu
  have hus : u ≤ s := (Finset.mem_Ico.mp hu).2.le
  unfold gapNewCoeff gapA
  rw [gapX_reflect hus, Real.mul_rpow (gapQ_pos hc).le hr, mul_pow,
    Real.mul_rpow (pow_nonneg (gapQ_pos hc).le _) (pow_nonneg (gapBeta_pos hc).le _),
    ← Real.rpow_pow_comm (gapQ_pos hc).le,
    ← Real.rpow_pow_comm (gapBeta_pos hc).le]
  ring

theorem pureCross_normalized_lt {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c)
    {θ r : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 1 ≤ r) :
    crossLayer (c + 1) (c - 1) s (gapQ c ^ θ) (r ^ θ) <
      crossLayer c c s (gapBeta c ^ θ) ((gapQ c * r) ^ θ) := by
  have hc : 2 ≤ c := by omega
  rw [crossLayer_gap_old hc, crossLayer_gap_new hc θ (by linarith)]
  apply gap_cross_normalized_lt hs hsc hθ hθ1
  exact Real.one_le_rpow hr hθ.le

theorem pureCross_scaled_lt {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c)
    {θ K r : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 0 < K) (hr : 1 ≤ r) :
    crossLayer (c + 1) (c - 1) s ((K * gapQ c) ^ θ) ((K * r) ^ θ) <
      crossLayer c c s ((K * gapBeta c) ^ θ) ((K * (gapQ c * r)) ^ θ) := by
  have hc : 2 ≤ c := by omega
  have hr0 : 0 ≤ r := by linarith
  rw [Real.mul_rpow hK.le (gapQ_pos hc).le, Real.mul_rpow hK.le hr0,
    Real.mul_rpow hK.le (gapBeta_pos hc).le,
    Real.mul_rpow hK.le (mul_nonneg (gapQ_pos hc).le hr0),
    crossLayer_scale, crossLayer_scale]
  exact mul_lt_mul_of_pos_left (pureCross_normalized_lt hs hsc hθ hθ1 hr)
    (pow_pos (Real.rpow_pos_of_pos hK θ) s)

theorem pureCross_mass_lt {c s : ℕ} (hs : 3 ≤ s) (hsc : s ≤ c)
    {θ A B : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hA : 0 < A)
    (hAB : (c : ℝ) / ((c : ℝ) + 1) * A ≤ B) :
    crossLayer (c + 1) (c - 1) s
        ((A / ((c : ℝ) + 1)) ^ θ) ((B / ((c : ℝ) - 1)) ^ θ) <
      crossLayer c c s ((A / (c : ℝ)) ^ θ) ((B / (c : ℝ)) ^ θ) := by
  have hc : 3 ≤ c := hs.trans hsc
  have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := by linarith
  have hcp : 0 < (c : ℝ) + 1 := by linarith
  have hcm : 0 < (c : ℝ) - 1 := by linarith
  let K : ℝ := A * c / (((c : ℝ) + 1) * ((c : ℝ) - 1))
  let r : ℝ := B * ((c : ℝ) + 1) / (A * c)
  have hK : 0 < K := div_pos (mul_pos hA hc0) (mul_pos hcp hcm)
  have hr : 1 ≤ r := by
    apply (one_le_div (mul_pos hA hc0)).2
    have hAB' : A * (c : ℝ) / ((c : ℝ) + 1) ≤ B := by
      calc
        _ = (c : ℝ) / ((c : ℝ) + 1) * A := by ring
        _ ≤ B := hAB
    have h := (div_le_iff₀ hcp).mp hAB'
    exact h
  have heq1 : K * gapQ c = A / ((c : ℝ) + 1) := by
    dsimp [K, gapQ]
    field_simp <;> ring
  have heq2 : K * r = B / ((c : ℝ) - 1) := by
    dsimp [K, r]
    field_simp
  have heq3 : K * gapBeta c = A / (c : ℝ) := by
    dsimp [K, gapBeta]
    field_simp <;> ring
  have heq4 : K * (gapQ c * r) = B / (c : ℝ) := by
    dsimp [K, r, gapQ]
    field_simp <;> ring
  have h := pureCross_scaled_lt hs hsc hθ hθ1 hK hr
  rwa [heq1, heq2, heq3, heq4] at h

end ChromaticSpectral
