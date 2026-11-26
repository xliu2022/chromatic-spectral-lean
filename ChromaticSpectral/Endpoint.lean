module

public import ChromaticSpectral.Curvature
public import ChromaticSpectral.ChooseConvexity
public import ChromaticSpectral.Interpolation
public import ChromaticSpectral.SymmetricMean

/-!
# Estimates for the endpoint in the explicit Lagrangian bound

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem endpointProfile_global {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    (y - a) / y ^ 4 ≤ 27 / (256 * a ^ 3) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have h := mul_nonneg (sq_nonneg (3 * y - 4 * a))
    (show 0 ≤ 3 * y ^ 2 + 8 * a * y + 16 * a ^ 2 by positivity)
  nlinarith only [h]

theorem endpointProfile_le_at_left {a q y : ℝ}
    (ha : 0 < a) (hq : 4 * a ≤ 3 * q) (hy : q ≤ y) :
    (y - a) / y ^ 4 ≤ (q - a) / q ^ 4 := by
  have hq0 : 0 < q := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hq0 hy
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hd : 0 ≤ y - q := sub_nonneg.mpr hy
  have hqa : 0 ≤ q - a := by linarith
  have hlin : 0 ≤ 3 * q - 4 * a := by linarith
  have h : 0 ≤ (y - q) * q ^ 3 * (3 * q - 4 * a) +
      6 * (y - q) ^ 2 * q ^ 2 * (q - a) +
      4 * (y - q) ^ 3 * q * (q - a) + (y - q) ^ 4 * (q - a) := by positivity
  nlinarith only [h]

/-- The logarithmic step in Claim 6.8 follows directly from Bernoulli. -/
theorem bernoulli_reciprocal_strict (a : ℕ) (ha : 0 < a) {q : ℝ} (hq : 0 < q) :
    (1 - (a : ℝ) / q) * (1 + 1 / q) ^ a < 1 := by
  have hq1 : 0 < q + 1 := by linarith
  have hi : 1 / (q + 1) ≤ 1 := (div_le_one hq1).2 (by linarith)
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (q + 1)) by linarith) a
  have hd : (a : ℝ) / (q + 1) < (a : ℝ) / q :=
    div_lt_div_of_pos_left (by exact_mod_cast ha) hq (by linarith)
  simp only [mul_neg, ← sub_eq_add_neg, mul_one_div] at hb
  have hl : 1 - (a : ℝ) / q < (1 - 1 / (q + 1)) ^ a := by
    nlinarith only [hb, hd]
  have hz : 0 < (1 + 1 / q) ^ a := by positivity
  have hmul := mul_lt_mul_of_pos_right hl hz
  have heq : (1 - 1 / (q + 1)) * (1 + 1 / q) = 1 := by field_simp; ring
  rw [← mul_pow, heq, one_pow] at hmul
  exact hmul

theorem one_add_inv_pow_lt_four (a : ℕ) {q : ℝ} (ha : 1 ≤ a) (hq : (a : ℝ) ≤ q) :
    (1 + 1 / q) ^ a < 4 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hq0 : 0 < q := lt_of_lt_of_le ha0 hq
  have hbase : 1 + 1 / q ≤ 1 + (a : ℝ)⁻¹ := by
    rw [← one_div]
    linarith [one_div_le_one_div_of_le ha0 hq]
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 + 1 / q by positivity) hbase a
  exact lt_of_le_of_lt (hp.trans (Real.one_add_inv_pow_le_exp (n := a)))
    (lt_trans Real.exp_one_lt_three (by norm_num))

/-- The analytic comparison inside Claim 6.8, without maximization operators. -/
theorem endpointProfile_strict (a : ℕ) (ha : 2 ≤ a) {q y : ℝ}
    (hq : (a : ℝ) ≤ q) (hy : q ≤ y) :
    (y - a) / y ^ 4 < 1 / (q ^ 3 * (1 + 1 / q) ^ a) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hq0 : 0 < q := lt_of_lt_of_le ha0 hq
  have hy0 : 0 < y := lt_of_lt_of_le hq0 hy
  by_cases hcase : 3 * q ≤ 4 * (a : ℝ)
  · have hg := endpointProfile_global ha0 hy0
    have hp := one_add_inv_pow_lt_four a (by omega) hq
    have hq3 : q ^ 3 ≤ (4 * (a : ℝ) / 3) ^ 3 := by
      apply pow_le_pow_left₀ (le_of_lt hq0) (by linarith)
    have hmid : 27 / (256 * (a : ℝ) ^ 3) ≤ 1 / (4 * q ^ 3) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [hq3]
    have hlast : 1 / (4 * q ^ 3) < 1 / (q ^ 3 * (1 + 1 / q) ^ a) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith [mul_pos (pow_pos hq0 3) (sub_pos.mpr hp)]
    exact lt_of_le_of_lt (hg.trans hmid) hlast
  · have hg := endpointProfile_le_at_left ha0 (by linarith) hy
    have hb := bernoulli_reciprocal_strict a (by omega) hq0
    have hlast : (q - (a : ℝ)) / q ^ 4 < 1 / (q ^ 3 * (1 + 1 / q) ^ a) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      calc
        (q - (a : ℝ)) * (q ^ 3 * (1 + 1 / q) ^ a) =
            ((1 - (a : ℝ) / q) * (1 + 1 / q) ^ a) * q ^ 4 := by field_simp
        _ < 1 * q ^ 4 := mul_lt_mul_of_pos_right hb (pow_pos hq0 4)
    exact lt_of_le_of_lt hg hlast

theorem endpoint_choose_lower (r q : ℕ) (hr : 3 ≤ r) (hq : r - 1 ≤ q) :
    q ^ (r - 2) ≤ (r - 2).factorial * (2 * q - 2).choose (r - 2) := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  calc
    q ^ (r - 2) = ∏ _ ∈ Finset.range (r - 2), q := by simp
    _ ≤ ∏ i ∈ Finset.range (r - 2), (2 * q - 2 - i) := by
      apply Finset.prod_le_prod
      intro i hi
      have hi' := Finset.mem_range.mp hi
      omega

theorem reciprocal_power_rewrite {q : ℝ} (hq : q ≠ 0) (m : ℕ) (F : ℝ) :
    (1 / (q ^ 3 * (1 + 1 / q) ^ (m + 1))) / F =
      (q ^ m / F) / (q ^ 2 * (q + 1) ^ (m + 1)) := by
  have he : 1 + 1 / q = (q + 1) / q := by field_simp
  rw [he, div_pow, pow_succ, pow_succ]
  field_simp
  <;> ring

/-- Claim 6.8 in pointwise form (in fact valid for all `y ≥ q`). -/
theorem endpoint_curvature_bound (r q : ℕ) (hr : 3 ≤ r) (hq : r - 1 ≤ q)
    {y : ℝ} (hy : (q : ℝ) ≤ y) :
    (y - r + 1) / (((r - 2).factorial : ℝ) * y ^ 4) <
      ((2 * q - 2).choose (r - 2) : ℝ) /
        ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ (r - 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hprof := endpointProfile_strict (r - 1) (by omega) (q := (q : ℝ))
    (by exact_mod_cast hq) hy
  rw [hcast] at hprof
  have hfac : (0 : ℝ) < (r - 2).factorial := by positivity
  have hchoose : (q : ℝ) ^ (r - 2) / ((r - 2).factorial : ℝ) ≤
      ((2 * q - 2).choose (r - 2) : ℝ) := by
    apply (div_le_iff₀ hfac).2
    have hh : (q : ℝ) ^ (r - 2) ≤
        ((r - 2).factorial : ℝ) * ((2 * q - 2).choose (r - 2) : ℝ) := by
      exact_mod_cast endpoint_choose_lower r q hr hq
    simpa only [mul_comm] using hh
  calc
    (y - r + 1) / (((r - 2).factorial : ℝ) * y ^ 4) =
        ((y - ((r : ℝ) - 1)) / y ^ 4) / ((r - 2).factorial : ℝ) := by ring
    _ < (1 / ((q : ℝ) ^ 3 * (1 + 1 / (q : ℝ)) ^ (r - 1))) /
        ((r - 2).factorial : ℝ) := div_lt_div_of_pos_right hprof hfac
    _ = ((q : ℝ) ^ (r - 2) / ((r - 2).factorial : ℝ)) /
        ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ (r - 1)) := by
      rw [show r - 1 = (r - 2) + 1 by omega]
      exact reciprocal_power_rewrite hq0.ne' _ _
    _ ≤ ((2 * q - 2).choose (r - 2) : ℝ) /
        ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ (r - 1)) :=
      div_le_div_of_nonneg_right hchoose (by positivity)

theorem endpoint_choose_ratio (r q : ℕ) (hr : 4 ≤ r) (hq : r - 1 ≤ q) :
    (q + 1) * (2 * q - 2).choose (r - 2) ≤
      q * (2 * q - 1).choose (r - 2) := by
  have hq3 : 3 ≤ q := by omega
  have hdeg : r - 2 ≤ 2 * q - 2 := by omega
  have h := Nat.choose_mul_succ_eq (2 * q - 2) (r - 2)
  rw [show 2 * q - 2 + 1 = 2 * q - 1 by omega] at h
  have hsub : 2 * q - 1 - (r - 2) + r = 2 * q + 1 := by omega
  have hbase : 2 * q - 1 + 1 = 2 * q := by omega
  have hf : (q + 1) * (2 * q - 1 - (r - 2)) ≤ q * (2 * q - 1) := by
    have hm := Nat.mul_le_mul_right q hr
    nlinarith [congrArg (fun z : ℕ => q * z) hsub,
      congrArg (fun z : ℕ => q * z) hbase]
  have hp : 0 < 2 * q - 1 - (r - 2) := by omega
  apply Nat.le_of_mul_le_mul_right (c := 2 * q - 1 - (r - 2))
  · nlinarith [Nat.mul_le_mul_right ((2 * q - 2).choose (r - 2)) hf]
  · exact hp

/-- The numerical comparison (6.24), for the parameter range of the main theorem. -/
theorem endpoint_coefficient_comparison (r q n : ℕ) (hr : 4 ≤ r) (hq : r - 1 ≤ q)
    (hn : 2 * q + 1 ≤ n) {ν : ℝ} (hν : 0 < ν) (hν1 : ν < (q : ℝ) + 1) :
    ((2 * q - 2).choose (r - 2) : ℝ) /
        ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ (r - 1)) <
      ((n - 2).choose (r - 2) : ℝ) /
        ((q : ℝ) * ((q : ℝ) + 1) ^ (r - 1) * ν) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hc0 : (0 : ℝ) < (n - 2).choose (r - 2) := by
    exact_mod_cast Nat.choose_pos (show r - 2 ≤ n - 2 by omega)
  have hrat : ((q : ℝ) + 1) * ((2 * q - 2).choose (r - 2) : ℝ) ≤
      (q : ℝ) * ((n - 2).choose (r - 2) : ℝ) := by
    have h1 := endpoint_choose_ratio r q hr hq
    have h2 := Nat.choose_le_choose (r - 2) (show 2 * q - 1 ≤ n - 2 by omega)
    exact_mod_cast h1.trans (Nat.mul_le_mul_left q h2)
  have hmid : ((2 * q - 2).choose (r - 2) : ℝ) / (q : ℝ) ≤
      ((n - 2).choose (r - 2) : ℝ) / ((q : ℝ) + 1) := by
    apply (div_le_div_iff₀ hq0 hq1).2
    nlinarith only [hrat]
  have hlast := div_lt_div_of_pos_left hc0 hν hν1
  have hdiv := div_lt_div_of_pos_right (lt_of_le_of_lt hmid hlast)
    (show (0 : ℝ) < (q : ℝ) * ((q : ℝ) + 1) ^ (r - 1) by positivity)
  convert! hdiv using 1 <;> field_simp <;> ring

theorem normalizedChoose_twice_differentiable (r : ℕ) (hr : 1 ≤ r)
    {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (normalizedChoose r) x ∧
      DifferentiableAt ℝ (deriv (normalizedChoose r)) x := by
  let P : Polynomial ℝ := Polynomial.C ((r.factorial : ℝ)⁻¹) * ascPochhammer ℝ r
  have hf : normalizedChoose r = fun y => P.eval (y - ((r : ℝ) - 1)) / y ^ r := by
    funext y
    rw [normalizedChoose_eq]
    simp only [P, Polynomial.eval_mul, Polynomial.eval_C,
      show y - ((r : ℝ) - 1) = y - r + 1 by ring]
    ring
  rw [hf]
  exact ⟨(hasDerivAt_polynomial_div_pow P _ r hr hx).differentiableAt,
    (hasDerivAt_deriv_polynomial_div_pow P _ r hr hx).differentiableAt⟩

theorem normalizedChoose_interpolation_le (r q : ℕ) (hr : 3 ≤ r)
    (hq : r - 1 ≤ q) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    normalizedChoose r ((q : ℝ) + α) - (1 - α) * normalizedChoose r q -
        α * normalizedChoose r ((q : ℝ) + 1) ≤
      (((2 * q - 2).choose (r - 2) : ℝ) /
        ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ (r - 1))) / 2 * α * (1 - α) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply interpolation_defect_le hα0 hα1
  · change ContinuousOn (fun x : ℝ => Ring.choose x r / x ^ r)
      (Set.Icc (q : ℝ) ((q : ℝ) + 1))
    apply (realChoose_continuous r).continuousOn.div (continuous_pow r).continuousOn
    intro x hx
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hq0 hx.1))
  · intro y hy
    exact (normalizedChoose_twice_differentiable r (by omega) (by have := hy.1; linarith)).1
  · intro y hy
    exact (normalizedChoose_twice_differentiable r (by omega) (by have := hy.1; linarith)).2
  · intro y hy
    have hqr : (r : ℝ) - 1 ≤ (q : ℝ) := by
      have h : (r : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast (show r ≤ q + 1 by omega)
      linarith
    have h1 := normalizedChoose_curvature r hr (le_trans hqr hy.1.le)
    have h2 := endpoint_curvature_bound r q hr hq hy.1.le
    change -(deriv (deriv (normalizedChoose r))) y ≤ _ at h1
    linarith

/-- The endpoint gap obtained by comparing quantitative Maclaurin with the
second-derivative interpolation bound. -/
theorem endpoint_esymm_strict {V : Type*} [DecidableEq V]
    (s : Finset V) (w : V → ℝ) (r q : ℕ) (hr : 4 ≤ r) (hq : r - 1 ≤ q)
    (hn : 2 * q + 1 ≤ s.card) {α k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hk : 0 < k)
    (hw : ∀ v ∈ s, 1 / ((q : ℝ) + 1) ≤ w v)
    (hmean : ∑ v ∈ s, w v = (s.card : ℝ) * (1 / ((q : ℝ) + α)))
    (hvar : ∑ v ∈ s, (w v - 1 / ((q : ℝ) + α)) ^ 2 =
      k * α * (1 - α) / ((q : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + α))) :
    esymmOn s r w < (s.card.choose r : ℝ) / ((q : ℝ) + α) ^ r -
      k * normalizedChoose r ((q : ℝ) + α) +
      k * (1 - α) * normalizedChoose r q + k * α * normalizedChoose r ((q : ℝ) + 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hν : (0 : ℝ) < (q : ℝ) + α := by positivity
  have hα : 0 < 1 - α := sub_pos.mpr hα1
  let M : ℝ := ((2 * q - 2).choose (r - 2) : ℝ) /
    ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ (r - 1))
  let D : ℝ := ((s.card - 2).choose (r - 2) : ℝ) /
    ((q : ℝ) * ((q : ℝ) + 1) ^ (r - 1) * ((q : ℝ) + α))
  have hMD : M < D := endpoint_coefficient_comparison r q s.card hr hq hn hν (by linarith)
  have hM := normalizedChoose_interpolation_le r q (by omega) hq hα0.le hα1.le
  have hM' := mul_le_mul_of_nonneg_left hM hk.le
  have hD := esymmOn_variance_deficit (s := s) (x := w)
    (by omega) (show (0 : ℝ) ≤ 1 / ((q : ℝ) + 1) by positivity) hw hmean (r - 2)
  rw [hvar, Nat.sub_add_cancel (by omega : 2 ≤ r), one_div_pow] at hD
  have he : (1 / 2 : ℝ) * ((s.card - 2).choose (r - 2) : ℝ) *
      (1 / ((q : ℝ) + 1) ^ (r - 2)) *
      (k * α * (1 - α) / ((q : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + α))) =
        k * α * (1 - α) / 2 * D := by
    dsimp [D]
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    field_simp
    <;> ring
  rw [he, one_div_pow] at hD
  have hstrict := mul_lt_mul_of_pos_left hMD
    (show 0 < k * α * (1 - α) / 2 by positivity)
  change _ ≤ k * (M / 2 * α * (1 - α)) at hM'
  simp only [mul_one_div] at hD
  nlinarith only [hD, hM', hstrict]

end ChromaticSpectral
