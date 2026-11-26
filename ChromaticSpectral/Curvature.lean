module

public import ChromaticSpectral.RealChoose

/-!
# Algebraic curvature certificate for normalized real binomial coefficients

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators
open Polynomial

namespace ChromaticSpectral

def CoeffNonneg (P : Polynomial ℝ) : Prop := ∀ j, 0 ≤ P.coeff j

theorem CoeffNonneg.add {P Q : Polynomial ℝ}
    (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) : CoeffNonneg (P + Q) := by
  intro j
  simp only [coeff_add]
  exact add_nonneg (hP j) (hQ j)

theorem CoeffNonneg.mul {P Q : Polynomial ℝ}
    (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) : CoeffNonneg (P * Q) := by
  intro j
  rw [coeff_mul]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hP i.1) (hQ i.2)

theorem coeffNonneg_C {c : ℝ} (hc : 0 ≤ c) : CoeffNonneg (C c) := by
  intro j
  simp only [coeff_C]
  split_ifs <;> positivity

theorem coeffNonneg_X : CoeffNonneg (X : Polynomial ℝ) := by
  intro j
  simp only [coeff_X]
  split_ifs <;> positivity

theorem coeffNonneg_ascPochhammer (r : ℕ) : CoeffNonneg (ascPochhammer ℝ r) := by
  induction r with
  | zero => simpa using coeffNonneg_C (show (0 : ℝ) ≤ 1 by norm_num)
  | succ r ih =>
    rw [ascPochhammer_succ_right]
    exact ih.mul (coeffNonneg_X.add (by simpa using coeffNonneg_C (Nat.cast_nonneg r)))

theorem CoeffNonneg.eval_nonneg {P : Polynomial ℝ} (hP : CoeffNonneg P)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ P.eval x := by
  rw [eval_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hP i) (pow_nonneg hx i)

theorem ascPochhammer_coeff_succ (s j : ℕ) :
    (ascPochhammer ℝ (s + 1)).coeff (j + 1) =
      (ascPochhammer ℝ s).coeff j + s * (ascPochhammer ℝ s).coeff (j + 1) := by
  rw [ascPochhammer_succ_right, mul_add]
  simp [coeff_mul_X, mul_comm]

theorem ascPochhammer_coeff_zero {s : ℕ} (hs : 0 < s) :
    (ascPochhammer ℝ s).coeff 0 = 0 := by
  simpa only [← Polynomial.coeff_zero_eq_eval_zero] using
    (ascPochhammer_ne_zero_eval_zero (S := ℝ) hs.ne')

theorem ascPochhammer_natDegree (s : ℕ) : (ascPochhammer ℝ s).natDegree = s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [ascPochhammer_succ_right, ← C_eq_natCast,
      natDegree_mul (monic_ascPochhammer ℝ s).ne_zero (monic_X_add_C _).ne_zero,
      natDegree_X_add_C, ih]

/-- The coefficient inequality required in the induction of Claim 6.7.
It is proved directly by the rising-factorial recurrence, without Newton's inequalities. -/
theorem ascPochhammer_adjacent_coeff (s m : ℕ) (hm : m + 2 ≤ s) :
    2 * ((s : ℝ) - m) * (ascPochhammer ℝ s).coeff (m + 1) ≤
      (2 * s - 1) * (m + 2) * (ascPochhammer ℝ s).coeff (m + 2) := by
  induction s generalizing m with
  | zero => omega
  | succ s ih =>
    have hs : 1 ≤ s := by omega
    rw [ascPochhammer_coeff_succ, show m + 2 = (m + 1) + 1 by omega,
      ascPochhammer_coeff_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    by_cases hm0 : m = 0
    · subst m
      rw [ascPochhammer_coeff_zero (by omega)]
      by_cases hs1 : s = 1
      · subst s
        norm_num [coeff_X]
      · have hi := ih 0 (by omega)
        have hc := coeffNonneg_ascPochhammer s 1
        have hd := coeffNonneg_ascPochhammer s 2
        norm_num at hi ⊢
        have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
        nlinarith [mul_nonneg (show 0 ≤ (s : ℝ) from Nat.cast_nonneg s) (sub_nonneg.mpr hi)]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hprev := ih j (by omega)
      have hc := coeffNonneg_ascPochhammer s (j + 2)
      have hd := coeffNonneg_ascPochhammer s (j + 3)
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hprev ⊢
      by_cases htop : j + 3 ≤ s
      · have hnext := ih (j + 1) htop
        simp only [Nat.cast_add, Nat.cast_one] at hnext
        have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
        have hjr : (j : ℝ) + 3 ≤ s := by exact_mod_cast htop
        have hp := mul_nonneg (show 0 ≤ (2 * (s : ℝ) - 1) from by linarith)
          (sub_nonneg.mpr hprev)
        have hn := mul_nonneg (show 0 ≤ (s : ℝ) * (2 * s + 1) from by positivity)
          (sub_nonneg.mpr hnext)
        have hc' := mul_nonneg
          (show 0 ≤ (2 * (s : ℝ) - 1) * (2 * j + 5) + 4 * s * (s - (j + 1)) from
            by
              have : 0 ≤ (s : ℝ) - (j + 1) := by linarith
              have : 0 ≤ 2 * (s : ℝ) - 1 := by linarith
              positivity)
          hc
        nlinarith
      · have heq : s = j + 2 := by omega
        subst s
        have hdeg : (ascPochhammer ℝ (j + 2)).coeff (j + 3) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [ascPochhammer_natDegree]
          omega
        simp only [hdeg, mul_zero, add_zero, Nat.cast_add, Nat.cast_ofNat,
          show j + 1 + 1 = j + 2 by omega]
        simp only [Nat.cast_add, Nat.cast_ofNat] at hprev hc
        nlinarith

theorem coeff_X_mul_derivative (P : Polynomial ℝ) (m : ℕ) :
    (X * P.derivative).coeff m = (m : ℝ) * P.coeff m := by
  cases m with
  | zero => simp
  | succ m => simp [coeff_X_mul, coeff_derivative, mul_comm]

noncomputable def curvatureA (s : ℕ) : Polynomial ℝ :=
  (C 2 * X + C (2 * (s : ℝ) - 1)) * (ascPochhammer ℝ s).derivative.derivative -
    C (2 * (s : ℝ)) * (ascPochhammer ℝ s).derivative

theorem curvatureA_coeff (s m : ℕ) :
    (curvatureA s).coeff m = (m + 1 : ℝ) *
      ((2 * s - 1) * (m + 2) * (ascPochhammer ℝ s).coeff (m + 2) -
        2 * (s - m) * (ascPochhammer ℝ s).coeff (m + 1)) := by
  unfold curvatureA
  rw [add_mul, mul_assoc]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative,
    Nat.cast_add, Nat.cast_one]
  ring

theorem curvatureA_top_correction_nonneg (s : ℕ) (hs : 2 ≤ s) :
    CoeffNonneg (curvatureA s + C (2 * (s : ℝ)) * X ^ (s - 1)) := by
  intro m
  rw [coeff_add, curvatureA_coeff, coeff_C_mul, coeff_X_pow]
  by_cases hl : m + 2 ≤ s
  · have hm : ¬m = s - 1 := by omega
    rw [if_neg hm]
    simp only [mul_zero, add_zero]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (ascPochhammer_adjacent_coeff s m hl))
  · by_cases ht : m + 1 = s
    · have hlead : (ascPochhammer ℝ s).coeff (m + 1) = 1 := by
        simpa only [ascPochhammer_natDegree, ht] using
          (monic_ascPochhammer ℝ s).coeff_natDegree
      have hz : (ascPochhammer ℝ s).coeff (m + 2) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [ascPochhammer_natDegree]
        omega
      rw [hlead, hz, if_pos (by omega : m = s - 1)]
      have hsr : (s : ℝ) = m + 1 := by exact_mod_cast ht.symm
      nlinarith
    · have hz1 : (ascPochhammer ℝ s).coeff (m + 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [ascPochhammer_natDegree]
        omega
      have hz2 : (ascPochhammer ℝ s).coeff (m + 2) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [ascPochhammer_natDegree]
        omega
      simp [hz1, hz2, show m ≠ s - 1 by omega]

noncomputable def curvatureRemainder (s : ℕ) : Polynomial ℝ :=
  C ((s : ℝ) + 1) * (X + C (s : ℝ)) ^ (s - 2) -
    C ((s : ℝ) - 1) * (X + C ((s : ℝ) - 1)) ^ (s - 2) -
    C 2 * X ^ (s - 2)

theorem curvatureRemainder_nonneg (s : ℕ) (hs : 2 ≤ s) :
    CoeffNonneg (curvatureRemainder s) := by
  intro j
  simp only [curvatureRemainder, coeff_sub, coeff_C_mul, coeff_X_add_C_pow, coeff_X_pow]
  by_cases hj : s - 2 = j
  · subst j
    simp
    ring_nf
    exact le_refl 2
  · rw [if_neg (Ne.symm hj), mul_zero, sub_zero]
    have hs0 : 0 ≤ (s : ℝ) - 1 := by
      have : (1 : ℝ) ≤ s := by exact_mod_cast (show (1 : ℕ) ≤ s by omega)
      linarith
    have hp : ((s : ℝ) - 1) ^ (s - 2 - j) ≤ (s : ℝ) ^ (s - 2 - j) :=
      pow_le_pow_left₀ hs0 (by linarith) _
    have hmul : ((s : ℝ) - 1) * (((s : ℝ) - 1) ^ (s - 2 - j) * ((s - 2).choose j : ℝ)) ≤
        ((s : ℝ) + 1) * ((s : ℝ) ^ (s - 2 - j) * ((s - 2).choose j : ℝ)) := by
      apply mul_le_mul (by linarith)
        (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity) (by positivity)
    exact sub_nonneg.mpr hmul

noncomputable def curvatureDelta (s : ℕ) : Polynomial ℝ :=
  curvatureA s + C (s : ℝ) * X *
    (C ((s : ℝ) + 1) * (X + C (s : ℝ)) ^ (s - 2) -
      C ((s : ℝ) - 1) * (X + C ((s : ℝ) - 1)) ^ (s - 2))

theorem curvatureDelta_decomposition (s : ℕ) (hs : 2 ≤ s) :
    curvatureDelta s =
      (curvatureA s + C (2 * (s : ℝ)) * X ^ (s - 1)) +
        C (s : ℝ) * X * curvatureRemainder s := by
  unfold curvatureDelta curvatureRemainder
  rw [show s - 1 = (s - 2) + 1 by omega, pow_succ, map_mul]
  ring

theorem curvatureDelta_nonneg (s : ℕ) (hs : 2 ≤ s) : CoeffNonneg (curvatureDelta s) := by
  rw [curvatureDelta_decomposition s hs]
  exact (curvatureA_top_correction_nonneg s hs).add
    (((coeffNonneg_C (Nat.cast_nonneg s)).mul coeffNonneg_X).mul
      (curvatureRemainder_nonneg s hs))

/-- The polynomial `E_r` from equation (6.13). -/
noncomputable def curvatureCertificate (r : ℕ) : Polynomial ℝ :=
  (X + C ((r : ℝ) - 1)) ^ 2 * (ascPochhammer ℝ r).derivative.derivative -
    C (2 * (r : ℝ)) * (X + C ((r : ℝ) - 1)) * (ascPochhammer ℝ r).derivative +
    C ((r : ℝ) * (r + 1)) * ascPochhammer ℝ r +
    C ((r : ℝ) * (r - 1)) * X * (X + C ((r : ℝ) - 1)) ^ (r - 2)

theorem curvatureCertificate_three : curvatureCertificate 3 = 0 := by
  norm_num [curvatureCertificate, ascPochhammer_succ_right, derivative_mul,
    derivative_add, derivative_X, derivative_C, map_ofNat]
  ring

theorem curvatureCertificate_succ (s : ℕ) (hs : 3 ≤ s) :
    curvatureCertificate (s + 1) =
      (X + C (s : ℝ)) * (curvatureCertificate s + curvatureDelta s) := by
  have hs1 : s + 1 - 2 = s - 2 + 1 := by omega
  simp only [curvatureCertificate, curvatureDelta, curvatureA,
    ascPochhammer_succ_right, derivative_mul, derivative_add, derivative_X,
    derivative_natCast, derivative_one, derivative_zero, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, one_mul, Nat.cast_add, Nat.cast_one, hs1]
  simp only [add_sub_cancel_right, ← C_eq_natCast]
  rw [pow_succ]
  simp only [map_add, map_sub, map_mul, map_ofNat, map_one]
  ring

/-- The algebraic core of Claim 6.7, for every uniformity, not a finite check. -/
theorem curvatureCertificate_nonneg (r : ℕ) (hr : 3 ≤ r) :
    CoeffNonneg (curvatureCertificate r) := by
  induction r, hr using Nat.le_induction with
  | base => simp [curvatureCertificate_three, CoeffNonneg]
  | succ s hs ih =>
    rw [curvatureCertificate_succ s hs]
    exact (coeffNonneg_X.add (coeffNonneg_C (Nat.cast_nonneg s))).mul
      (ih.add (curvatureDelta_nonneg s (by omega)))

theorem curvatureCertificate_eval_nonneg (r : ℕ) (hr : 3 ≤ r)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (curvatureCertificate r).eval x :=
  (curvatureCertificate_nonneg r hr).eval_nonneg hx

theorem hasDerivAt_div_pow_succ {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (hx : x ≠ 0) (m : ℕ) :
    HasDerivAt (fun y => f y / y ^ (m + 1))
      ((x * f' - (m + 1 : ℝ) * f x) / x ^ (m + 2)) x := by
  have h := hf.div ((hasDerivAt_id x).pow (m + 1)) (pow_ne_zero _ hx)
  convert! h using 1
  simp only [Pi.pow_apply, Pi.div_apply, Pi.mul_apply, id_eq,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one]
  simp only [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  field_simp
  <;> ring

theorem hasDerivAt_polynomial_div_pow (P : Polynomial ℝ) (a : ℝ) (r : ℕ)
    (hr : 1 ≤ r) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => P.eval (y - a) / y ^ r)
      ((x * P.derivative.eval (x - a) - (r : ℝ) * P.eval (x - a)) /
        x ^ (r + 1)) x := by
  have hP : HasDerivAt (fun y => P.eval (y - a)) (P.derivative.eval (x - a)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (P.hasDerivAt (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    hasDerivAt_div_pow_succ hP hx m

theorem deriv_polynomial_div_pow (P : Polynomial ℝ) (a : ℝ) (r : ℕ)
    (hr : 1 ≤ r) {x : ℝ} (hx : x ≠ 0) :
    deriv (fun y => P.eval (y - a) / y ^ r) x =
      (x * P.derivative.eval (x - a) - (r : ℝ) * P.eval (x - a)) /
        x ^ (r + 1) :=
  (hasDerivAt_polynomial_div_pow P a r hr hx).deriv

theorem hasDerivAt_deriv_polynomial_div_pow (P : Polynomial ℝ) (a : ℝ) (r : ℕ)
    (hr : 1 ≤ r) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (deriv (fun y => P.eval (y - a) / y ^ r))
      ((x ^ 2 * P.derivative.derivative.eval (x - a) -
        2 * r * x * P.derivative.eval (x - a) +
        (r : ℝ) * (r + 1) * P.eval (x - a)) / x ^ (r + 2)) x := by
  have hP := (P.hasDerivAt (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  have hP' := (P.derivative.hasDerivAt (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  have hN := ((hasDerivAt_id x).mul hP').sub (hP.const_mul (r : ℝ))
  have h := hasDerivAt_div_pow_succ hN hx r
  have h' : HasDerivAt
      (fun y => (y * P.derivative.eval (y - a) - (r : ℝ) * P.eval (y - a)) / y ^ (r + 1))
      ((x ^ 2 * P.derivative.derivative.eval (x - a) -
        2 * r * x * P.derivative.eval (x - a) +
        (r : ℝ) * (r + 1) * P.eval (x - a)) / x ^ (r + 2)) x := by
    convert! h using 1 <;> simp only [Function.comp_def, id_eq, mul_one, one_mul,
      Pi.mul_apply, Pi.sub_apply]
    congr 1
    ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact deriv_polynomial_div_pow P a r hr hy

theorem deriv2_polynomial_div_pow (P : Polynomial ℝ) (a : ℝ) (r : ℕ)
    (hr : 1 ≤ r) {x : ℝ} (hx : x ≠ 0) :
    (deriv^[2] (fun y => P.eval (y - a) / y ^ r)) x =
      (x ^ 2 * P.derivative.derivative.eval (x - a) -
        2 * r * x * P.derivative.eval (x - a) +
        (r : ℝ) * (r + 1) * P.eval (x - a)) / x ^ (r + 2) := by
  exact (hasDerivAt_deriv_polynomial_div_pow P a r hr hx).deriv

theorem deriv2_normalizedChoose (r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx : x ≠ 0) :
    (deriv^[2] (normalizedChoose r)) x =
      (x ^ 2 * (ascPochhammer ℝ r).derivative.derivative.eval (x - r + 1) -
        2 * r * x * (ascPochhammer ℝ r).derivative.eval (x - r + 1) +
        (r : ℝ) * (r + 1) * (ascPochhammer ℝ r).eval (x - r + 1)) /
      ((r.factorial : ℝ) * x ^ (r + 2)) := by
  let P : Polynomial ℝ := C ((r.factorial : ℝ)⁻¹) * ascPochhammer ℝ r
  have hf : normalizedChoose r = fun y => P.eval (y - ((r : ℝ) - 1)) / y ^ r := by
    funext y
    rw [normalizedChoose_eq]
    simp only [P, eval_mul, eval_C, show y - ((r : ℝ) - 1) = y - r + 1 by ring]
    ring
  rw [hf, deriv2_polynomial_div_pow P ((r : ℝ) - 1) r hr hx]
  simp only [P, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
    show x - ((r : ℝ) - 1) = x - r + 1 by ring]
  ring

theorem factorial_two_factors (r : ℕ) (hr : 2 ≤ r) :
    (r.factorial : ℝ) = (r : ℝ) * (r - 1) * ((r - 2).factorial : ℝ) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2 + s - 2 = s by omega]
  simp only [show 2 + s = (s + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  ring

/-- Claim 6.7, including the endpoint `x = r - 1`. -/
theorem normalizedChoose_curvature (r : ℕ) (hr : 3 ≤ r) {x : ℝ}
    (hx : (r : ℝ) - 1 ≤ x) :
    -(deriv^[2] (normalizedChoose r)) x ≤
      (x - r + 1) / (((r - 2).factorial : ℝ) * x ^ 4) := by
  have hrr : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < x := by linarith
  have hxne := hx0.ne'
  have hE := curvatureCertificate_eval_nonneg r hr (x := x - r + 1) (by linarith)
  simp only [curvatureCertificate, eval_add, eval_sub, eval_mul, eval_pow, eval_X,
    eval_C, show x - (r : ℝ) + 1 + ((r : ℝ) - 1) = x by ring] at hE
  rw [deriv2_normalizedChoose r (by omega) hxne, ← neg_div]
  have hden : 0 < (r.factorial : ℝ) * x ^ (r + 2) := by positivity
  have hineq := (div_le_div_iff_of_pos_right hden).mpr
    (show -(x ^ 2 * (ascPochhammer ℝ r).derivative.derivative.eval (x - r + 1) -
      2 * r * x * (ascPochhammer ℝ r).derivative.eval (x - r + 1) +
      (r : ℝ) * (r + 1) * (ascPochhammer ℝ r).eval (x - r + 1)) ≤
        (r : ℝ) * (r - 1) * (x - r + 1) * x ^ (r - 2) by linarith)
  apply hineq.trans_eq
  rw [factorial_two_factors r (by omega), show r + 2 = (r - 2) + 4 by omega, pow_add]
  have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hr1]
  <;> ring

end ChromaticSpectral
