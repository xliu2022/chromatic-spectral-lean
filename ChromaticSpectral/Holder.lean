module

public import ChromaticSpectral.SpectralBasic

/-! # The finite Hölder reduction from p-spectral radius to the Lagrangian
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral

theorem scale_complementary_rpow {f A B t : ℝ} (hf : 0 < f)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (f * A) ^ (1 - t) * (f * B) ^ t = f * (A ^ (1 - t) * B ^ t) := by
  rw [Real.mul_rpow hf.le hA, Real.mul_rpow hf.le hB]
  calc
    f ^ (1 - t) * A ^ (1 - t) * (f ^ t * B ^ t) =
        (f ^ (1 - t) * f ^ t) * (A ^ (1 - t) * B ^ t) := by ring
    _ = f * (A ^ (1 - t) * B ^ t) := by
      rw [← Real.rpow_add hf, sub_add_cancel, Real.rpow_one]

namespace RGraph
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem edgePolynomial_holder (G : RGraph V r) {p : ℝ} (hp : 1 ≤ p)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    G.edgePolynomial x ≤ (G.edges.card : ℝ) ^ (1 - p⁻¹) *
      (G.edgePolynomial (fun v => (x v) ^ p)) ^ p⁻¹ := by
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg G.edges hp
    (fun _ : Finset V => (1 : ℝ)) (fun e => ∏ v ∈ e, x v)
    (fun _ => zero_le_one) (fun e => Finset.prod_nonneg (fun v _ => hx v))
  have hprod : ∀ e : Finset V, (∏ v ∈ e, x v) ^ p = ∏ v ∈ e, (x v) ^ p := by
    intro e
    exact (Real.finsetProd_rpow e x (fun v _ => hx v) p).symm
  simpa only [edgePolynomial, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hprod] using hh

/-- Lemma 2.6, with the harmless endpoint p = 1 also included. -/
theorem pSpectralRadius_holder (G : RGraph V r) {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p ≤ ((r.factorial : ℝ) * G.edges.card) ^ (1 - p⁻¹) *
      (G.pSpectralRadius 1) ^ p⁻¹ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hfac : 0 < (r.factorial : ℝ) := by positivity
  have hL : 0 ≤ G.pSpectralRadius 1 := G.pSpectralRadius_nonneg zero_lt_one
  apply (G.pSpectralRadius_le_iff hp0 (mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg hL _))).mpr
  intro x hx
  have hy : PWeights 1 (fun v => (x v) ^ p) := by
    constructor
    · exact fun v => Real.rpow_nonneg (hx.1 v) p
    · simpa only [Real.rpow_one] using hx.2
  have hpoly := G.polyform_le_pSpectralRadius zero_lt_one hy
  calc
    G.polyform x ≤ (r.factorial : ℝ) *
        ((G.edges.card : ℝ) ^ (1 - p⁻¹) * (G.edgePolynomial (fun v => (x v) ^ p)) ^ p⁻¹) :=
      mul_le_mul_of_nonneg_left (G.edgePolynomial_holder hp hx.1) hfac.le
    _ = ((r.factorial : ℝ) * G.edges.card) ^ (1 - p⁻¹) *
        (G.polyform (fun v => (x v) ^ p)) ^ p⁻¹ := by
      exact (scale_complementary_rpow hfac (Nat.cast_nonneg _)
        (G.edgePolynomial_nonneg hy.1)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (G.polyform_nonneg hy.1) hpoly (inv_nonneg.mpr hp0.le))
      (Real.rpow_nonneg (by positivity) _)

end RGraph
end ChromaticSpectral
