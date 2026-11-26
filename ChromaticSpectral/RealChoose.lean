module

public import ChromaticSpectral.Basic

/-!
# Real binomial coefficients used in the explicit spectral bound

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.

The real binomial coefficient is the descending-factorial polynomial divided
by the factorial. In particular, division in its argument is real division.
-/

@[expose] public section
open scoped BigOperators
open Polynomial

namespace ChromaticSpectral

theorem realChoose_eq_ascending (x : ℝ) (r : ℕ) :
    Ring.choose x r = (ascPochhammer ℝ r).eval (x - r + 1) / (r.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem realChoose_natCast (n r : ℕ) : Ring.choose (n : ℝ) r = (n.choose r : ℝ) :=
  Ring.choose_natCast n r

theorem ascPochhammer_eval_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    0 ≤ (ascPochhammer ℝ r).eval x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_nonneg ih (by positivity)

theorem ascPochhammer_eval_pos {x : ℝ} (hx : 0 < x) (r : ℕ) :
    0 < (ascPochhammer ℝ r).eval x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_pos ih (by positivity)

theorem realChoose_nonneg {x : ℝ} {r : ℕ} (hx : (r : ℝ) - 1 ≤ x) :
    0 ≤ Ring.choose x r := by
  rw [realChoose_eq_ascending]
  exact div_nonneg (ascPochhammer_eval_nonneg (by linarith) r) (by positivity)

theorem realChoose_pos {x : ℝ} {r : ℕ} (hx : (r : ℝ) - 1 < x) :
    0 < Ring.choose x r := by
  rw [realChoose_eq_ascending]
  exact div_pos (ascPochhammer_eval_pos (by linarith) r) (by positivity)

/-- The normalized generalized binomial coefficient appearing in Claim 6.7. -/
noncomputable def normalizedChoose (r : ℕ) (x : ℝ) : ℝ :=
  Ring.choose x r / x ^ r

theorem normalizedChoose_eq (r : ℕ) (x : ℝ) :
    normalizedChoose r x =
      (ascPochhammer ℝ r).eval (x - r + 1) / ((r.factorial : ℝ) * x ^ r) := by
  rw [normalizedChoose, realChoose_eq_ascending, div_div]

end ChromaticSpectral
