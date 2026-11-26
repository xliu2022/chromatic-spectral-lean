module

public import ChromaticSpectral.Holder
public import ChromaticSpectral.Normalization

/-!
# Explicit bounds through the finite Hölder inequality

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem complementary_power_scale {A N p d : ℝ} (hA : 0 < A) (hN : 0 < N)
    (hp : p ≠ 0) :
    A ^ (1 - p⁻¹) * (A * N ^ (-d)) ^ p⁻¹ = A * N ^ (-d / p) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _)]
  calc
    _ = (A ^ (1 - p⁻¹) * A ^ p⁻¹) * (N ^ (-d)) ^ p⁻¹ := by ring
    _ = A * N ^ (-d / p) := by
      rw [← Real.rpow_add hA, sub_add_cancel, Real.rpow_one, ← Real.rpow_mul hN.le]
      congr 2

theorem explicitBound_one (r k n : ℕ) :
    explicitBound r k n 1 = (r.factorial : ℝ) *
      ((n.choose r : ℝ) - (k : ℝ) * Ring.choose ((n : ℝ) / k) r) / (n : ℝ) ^ r := by
  simp only [explicitBound, div_one, Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]
  ring

namespace RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

/-- Evaluation at the uniform point supplies the usual elementary lower bound. -/
theorem uniform_spectral_lower [Nonempty V] (G : RGraph V r) {p : ℝ} (hp : 0 < p) :
    (r.factorial : ℝ) * G.edges.card *
      (Fintype.card V : ℝ) ^ (-(r : ℝ) / p) ≤ G.pSpectralRadius p := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hx : PWeights p (fun _ : V => (Fintype.card V : ℝ) ^ (-1 / p)) := by
    simpa only [Real.one_rpow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] using PWeights.normalize hp (x := fun _ : V => 1) (fun _ => zero_le_one)
      (by simpa using hN)
  have h := G.polyform_le_pSpectralRadius hp hx
  rw [polyform, edgePolynomial_const] at h
  have he : ((Fintype.card V : ℝ) ^ (-1 / p)) ^ r =
      (Fintype.card V : ℝ) ^ (-(r : ℝ) / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [he] at h
  simpa only [mul_assoc] using h

theorem pSpectralRadius_le_scaled_of_lagrangian_le (G : RGraph V r)
    {p A N : ℝ} (hp : 1 ≤ p) (hA : 0 < A) (hN : 0 < N)
    (hedges : (r.factorial : ℝ) * G.edges.card ≤ A)
    (hL : G.pSpectralRadius 1 ≤ A * N ^ (-(r : ℝ))) :
    G.pSpectralRadius p ≤ A * N ^ (-(r : ℝ) / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hi : 0 < p⁻¹ := inv_pos.mpr hp0
  have hi1 : p⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hp
  have hE := Real.rpow_le_rpow (show (0 : ℝ) ≤ (r.factorial : ℝ) * G.edges.card by positivity)
    hedges (sub_nonneg.mpr hi1)
  have hL0 := G.pSpectralRadius_nonneg (p := 1) zero_lt_one
  calc
    G.pSpectralRadius p ≤ ((r.factorial : ℝ) * G.edges.card) ^ (1 - p⁻¹) *
        (G.pSpectralRadius 1) ^ p⁻¹ := G.pSpectralRadius_holder hp
    _ ≤ A ^ (1 - p⁻¹) * (A * N ^ (-(r : ℝ))) ^ p⁻¹ :=
      mul_le_mul hE (Real.rpow_le_rpow hL0 hL hi.le)
        (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hA.le _)
    _ = _ := complementary_power_scale hA hN hp0.ne'

theorem pSpectralRadius_lt_scaled_of_lagrangian_lt (G : RGraph V r)
    {p A N : ℝ} (hp : 1 ≤ p) (hA : 0 < A) (hN : 0 < N)
    (hedges : (r.factorial : ℝ) * G.edges.card ≤ A)
    (hL : G.pSpectralRadius 1 < A * N ^ (-(r : ℝ))) :
    G.pSpectralRadius p < A * N ^ (-(r : ℝ) / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hi : 0 < p⁻¹ := inv_pos.mpr hp0
  have hi1 : p⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hp
  have hE := Real.rpow_le_rpow (show (0 : ℝ) ≤ (r.factorial : ℝ) * G.edges.card by positivity)
    hedges (sub_nonneg.mpr hi1)
  have hL0 := G.pSpectralRadius_nonneg (p := 1) zero_lt_one
  calc
    G.pSpectralRadius p ≤ ((r.factorial : ℝ) * G.edges.card) ^ (1 - p⁻¹) *
        (G.pSpectralRadius 1) ^ p⁻¹ := G.pSpectralRadius_holder hp
    _ ≤ A ^ (1 - p⁻¹) * (G.pSpectralRadius 1) ^ p⁻¹ :=
      mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hL0 _)
    _ < A ^ (1 - p⁻¹) * (A * N ^ (-(r : ℝ))) ^ p⁻¹ :=
      mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hL0 hL hi) (Real.rpow_pos_of_pos hA _)
    _ = _ := complementary_power_scale hA hN hp0.ne'

end RGraph
end ChromaticSpectral
