module

public import ChromaticSpectral.Curvature
public import ChromaticSpectral.ElementarySymmetric

/-!
# Strict convexity of generalized binomial coefficients divided by powers

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators
open Polynomial

namespace ChromaticSpectral

theorem ascPochhammer_eq_prod (r : ℕ) :
    ascPochhammer ℝ r = ∏ i ∈ Finset.range r, (X + C (i : ℝ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ascPochhammer_succ_right, Finset.prod_range_succ, ih, C_eq_natCast]

theorem ascPochhammer_coeff_eq_esymm (r j : ℕ) (hj : j ≤ r) :
    (ascPochhammer ℝ r).coeff j = esymmOn (Finset.range r) (r - j) (fun i => (i : ℝ)) := by
  rw [ascPochhammer_eq_prod]
  simpa only [Finset.card_range, esymmOn] using
    Finset.prod_X_add_C_coeff (Finset.range r) (fun i => (i : ℝ)) (by simpa using hj)

theorem sum_range_real_twice (r : ℕ) :
    2 * ∑ i ∈ Finset.range r, (i : ℝ) = (r : ℝ) * (r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

theorem ascPochhammer_mean_coeff (r j : ℕ) (hj : j + 2 ≤ r) :
    2 * ((r : ℝ) - j - 1) * (ascPochhammer ℝ r).coeff (j + 1) ≤
      (j + 2 : ℝ) * (r - 1) * (ascPochhammer ℝ r).coeff (j + 2) := by
  have h := esymmOn_adjacent_mean
    (s := Finset.range r) (x := fun i => (i : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (r - (j + 2))
  have hdeg : r - (j + 2) + 1 = r - (j + 1) := by omega
  rw [hdeg, ← ascPochhammer_coeff_eq_esymm r (j + 1) (by omega),
    ← ascPochhammer_coeff_eq_esymm r (j + 2) hj,
    esymmOn_one, Finset.card_range] at h
  have hcast : ((r - (j + 2) : ℕ) : ℝ) = (r : ℝ) - j - 2 := by
    rw [Nat.cast_sub hj, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [hcast] at h
  have hsum := sum_range_real_twice r
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  apply (mul_le_mul_iff_right₀ hr).mp
  have he := congrArg (fun z : ℝ => z * (j + 2) * (ascPochhammer ℝ r).coeff (j + 2)) hsum
  nlinarith only [h, he]

theorem ascPochhammer_coeff_two_gt_one (r : ℕ) (hr : 3 ≤ r) :
    (ascPochhammer ℝ r).coeff 1 < (ascPochhammer ℝ r).coeff 2 := by
  induction r, hr using Nat.le_induction with
  | base =>
    have he : ascPochhammer ℝ 3 = X ^ 3 + C 3 * X ^ 2 + C 2 * X := by
      norm_num [ascPochhammer_succ_right, map_ofNat]
      ring
    rw [he]
    norm_num [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X]
  | succ r hr ih =>
    rw [show 1 = 0 + 1 by omega, ascPochhammer_coeff_succ,
      show 2 = 1 + 1 by omega, ascPochhammer_coeff_succ]
    rw [ascPochhammer_coeff_zero (by omega)]
    have hc := coeffNonneg_ascPochhammer r 1
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    nlinarith [mul_pos hr0 (sub_pos.mpr ih)]

theorem coeff_X_sq_mul_second_derivative (P : Polynomial ℝ) (j : ℕ) :
    (X ^ 2 * P.derivative.derivative).coeff j =
      (j : ℝ) * (j - 1) * P.coeff j := by
  rw [pow_two, mul_assoc]
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_X_mul, coeff_X_mul_derivative, coeff_derivative]
    push_cast
    ring

noncomputable def chooseConvexityCertificate (r m : ℕ) : Polynomial ℝ :=
  (X + C ((r : ℝ) - 1)) ^ 2 * (ascPochhammer ℝ r).derivative.derivative -
    C (2 * (m : ℝ)) * (X + C ((r : ℝ) - 1)) * (ascPochhammer ℝ r).derivative +
    C ((m : ℝ) * (m + 1)) * ascPochhammer ℝ r

theorem chooseConvexityCertificate_coeff (r m j : ℕ) :
    (chooseConvexityCertificate r m).coeff j =
      ((r : ℝ) - 1) ^ 2 * (j + 1) * (j + 2) * (ascPochhammer ℝ r).coeff (j + 2) +
      2 * (r - 1) * (j + 1) * (j - m) * (ascPochhammer ℝ r).coeff (j + 1) +
      (j - m) * (j - m - 1) * (ascPochhammer ℝ r).coeff j := by
  have he : chooseConvexityCertificate r m =
      X ^ 2 * (ascPochhammer ℝ r).derivative.derivative +
      C (2 * ((r : ℝ) - 1)) * (X * (ascPochhammer ℝ r).derivative.derivative) +
      C (((r : ℝ) - 1) ^ 2) * (ascPochhammer ℝ r).derivative.derivative -
      C (2 * (m : ℝ)) * (X * (ascPochhammer ℝ r).derivative) -
      C (2 * (m : ℝ) * ((r : ℝ) - 1)) * (ascPochhammer ℝ r).derivative +
      C ((m : ℝ) * (m + 1)) * ascPochhammer ℝ r := by
    unfold chooseConvexityCertificate
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [he]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_sq_mul_second_derivative,
    coeff_X_mul_derivative, coeff_derivative, Nat.cast_add, Nat.cast_one]
  ring

theorem chooseConvexityCertificate_nonneg (r m : ℕ) (hr : 3 ≤ r) (hm : m ≤ r - 1) :
    CoeffNonneg (chooseConvexityCertificate r m) := by
  intro j
  rw [chooseConvexityCertificate_coeff]
  have ha : 0 ≤ (r : ℝ) - 1 := by
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hc0 := coeffNonneg_ascPochhammer r j
  have hc1 := coeffNonneg_ascPochhammer r (j + 1)
  have hc2 := coeffNonneg_ascPochhammer r (j + 2)
  by_cases hj : j < m
  · have hjr : j + 2 ≤ r := by omega
    have h := ascPochhammer_mean_coeff r j hjr
    have hmR : (m : ℝ) ≤ r - 1 := by
      have : (m : ℝ) + 1 ≤ r := by exact_mod_cast (show m + 1 ≤ r by omega)
      linarith
    have hjR : (j : ℝ) < m := by exact_mod_cast hj
    have h1 := mul_nonneg (show 0 ≤ ((r : ℝ) - 1) * (j + 1) by positivity)
      (sub_nonneg.mpr h)
    have h2 := mul_nonneg
      (show 0 ≤ 2 * ((r : ℝ) - 1) * (j + 1) * (r - 1 - m) by
        have : 0 ≤ (r : ℝ) - 1 - m := by linarith
        positivity) hc1
    have h3 := mul_nonneg
      (show 0 ≤ ((j : ℝ) - m) * (j - m - 1) by
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hc0
    nlinarith only [h1, h2, h3]
  · have hjR : (m : ℝ) ≤ j := by exact_mod_cast (Nat.le_of_not_gt hj)
    by_cases heq : j = m
    · subst j
      simp only [sub_self, mul_zero, zero_mul, add_zero]
      positivity
    · have hjR' : (m : ℝ) + 1 ≤ j := by exact_mod_cast (show m + 1 ≤ j by omega)
      have : 0 ≤ (j : ℝ) - m := by linarith
      have : 0 ≤ (j : ℝ) - m - 1 := by linarith
      positivity

theorem chooseConvexityCertificate_constant_pos (r m : ℕ) (hr : 3 ≤ r)
    (hm : m ≤ r - 1) : 0 < (chooseConvexityCertificate r m).coeff 0 := by
  rw [chooseConvexityCertificate_coeff, ascPochhammer_coeff_zero (by omega)]
  norm_num
  have hd := ascPochhammer_coeff_two_gt_one r hr
  have hc := coeffNonneg_ascPochhammer r 1
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hra : 0 < (r : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ r - 1 := by
    have : (m : ℝ) + 1 ≤ r := by exact_mod_cast (show m + 1 ≤ r by omega)
    linarith
  have h1 := mul_pos (show 0 < 2 * ((r : ℝ) - 1) ^ 2 by positivity) (sub_pos.mpr hd)
  have h2 := mul_nonneg (show 0 ≤ 2 * ((r : ℝ) - 1) * (r - 1 - m) by
      have : 0 ≤ (r : ℝ) - 1 - m := by linarith
      have : 0 ≤ (r : ℝ) - 1 := by linarith
      positivity) hc
  nlinarith only [h1, h2]

theorem CoeffNonneg.eval_pos_of_constant_pos {P : Polynomial ℝ} (hP : CoeffNonneg P)
    (h0 : 0 < P.coeff 0) {x : ℝ} (hx : 0 ≤ x) : 0 < P.eval x := by
  rw [eval_eq_sum]
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (hP j) (pow_nonneg hx j)
  · refine ⟨0, ?_, ?_⟩
    · exact mem_support_iff.mpr h0.ne'
    · simpa using h0

theorem chooseConvexityCertificate_eval_pos (r m : ℕ) (hr : 3 ≤ r) (hm : m ≤ r - 1)
    {x : ℝ} (hx : 0 ≤ x) : 0 < (chooseConvexityCertificate r m).eval x :=
  (chooseConvexityCertificate_nonneg r m hr hm).eval_pos_of_constant_pos
    (chooseConvexityCertificate_constant_pos r m hr hm) hx

theorem polynomial_shift_deriv (P : Polynomial ℝ) (a : ℝ) :
    deriv (fun y => P.eval (y - a)) = fun y => P.derivative.eval (y - a) := by
  funext x
  have h : HasDerivAt (fun y => P.eval (y - a)) (P.derivative.eval (x - a)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (P.hasDerivAt (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  exact h.deriv

theorem deriv2_polynomial_div_pow_all (P : Polynomial ℝ) (a : ℝ) (m : ℕ)
    {x : ℝ} (hx : x ≠ 0) :
    (deriv^[2] (fun y => P.eval (y - a) / y ^ m)) x =
      (x ^ 2 * P.derivative.derivative.eval (x - a) -
        2 * m * x * P.derivative.eval (x - a) +
        (m : ℝ) * (m + 1) * P.eval (x - a)) / x ^ (m + 2) := by
  cases m with
  | zero =>
    simp only [pow_zero, div_one, Nat.cast_zero, mul_zero, zero_mul, sub_zero,
      zero_add, add_zero]
    change deriv (deriv (fun y => P.eval (y - a))) x = _
    rw [polynomial_shift_deriv, polynomial_shift_deriv]
    field_simp
  | succ m => exact deriv2_polynomial_div_pow P a (m + 1) (by omega) hx

theorem deriv2_realChoose_div_pow (r m : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (deriv^[2] (fun y => Ring.choose y r / y ^ m)) x =
      (x ^ 2 * (ascPochhammer ℝ r).derivative.derivative.eval (x - r + 1) -
        2 * m * x * (ascPochhammer ℝ r).derivative.eval (x - r + 1) +
        (m : ℝ) * (m + 1) * (ascPochhammer ℝ r).eval (x - r + 1)) /
      ((r.factorial : ℝ) * x ^ (m + 2)) := by
  let P : Polynomial ℝ := C ((r.factorial : ℝ)⁻¹) * ascPochhammer ℝ r
  have hf : (fun y => Ring.choose y r / y ^ m) =
      fun y => P.eval (y - ((r : ℝ) - 1)) / y ^ m := by
    funext y
    rw [realChoose_eq_ascending]
    simp only [P, eval_mul, eval_C, show y - ((r : ℝ) - 1) = y - r + 1 by ring]
    ring
  rw [hf, deriv2_polynomial_div_pow_all P ((r : ℝ) - 1) m hx]
  simp only [P, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
    show x - ((r : ℝ) - 1) = x - r + 1 by ring]
  ring

theorem realChoose_continuous (r : ℕ) : Continuous (fun x : ℝ => Ring.choose x r) := by
  have hf : (fun x : ℝ => Ring.choose x r) =
      fun x : ℝ => (ascPochhammer ℝ r).eval (x - (r : ℝ) + 1) / (r.factorial : ℝ) := by
    funext x
    exact realChoose_eq_ascending x r
  rw [hf]
  fun_prop

theorem realChoose_div_pow_deriv2_pos (r m : ℕ) (hr : 3 ≤ r) (hm : m ≤ r - 1)
    {x : ℝ} (hx : (r : ℝ) - 1 ≤ x) :
    0 < (deriv^[2] (fun y => Ring.choose y r / y ^ m)) x := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < x := by linarith
  rw [deriv2_realChoose_div_pow r m hx0.ne']
  apply div_pos _ (by positivity)
  have h := chooseConvexityCertificate_eval_pos r m hr hm (x := x - r + 1) (by linarith)
  simpa only [chooseConvexityCertificate, eval_add, eval_sub, eval_mul, eval_pow,
    eval_X, eval_C, show x - (r : ℝ) + 1 + ((r : ℝ) - 1) = x by ring] using h

/-- The strict convexity used for every Bernstein coefficient except the last. -/
theorem realChoose_div_pow_strictConvex (r m : ℕ) (hr : 3 ≤ r) (hm : m ≤ r - 1) :
    StrictConvexOn ℝ (Set.Ici ((r : ℝ) - 1)) (fun x => Ring.choose x r / x ^ m) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici _) ?_ ?_
  · apply (realChoose_continuous r).continuousOn.div (continuous_pow m).continuousOn
    intro x hx
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    exact pow_ne_zero _ (show x ≠ 0 by have := hx; simp only [Set.mem_Ici] at this; linarith)
  · intro x hx
    exact realChoose_div_pow_deriv2_pos r m hr hm (interior_subset hx)

end ChromaticSpectral
