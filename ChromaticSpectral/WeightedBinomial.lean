module

public import ChromaticSpectral.ExtremalColoring

/-! # From one-vertex optimality to the local mass ratio
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral

theorem descFactorial_mul_pow_le (a b s : ℕ) (hba : b ≤ a) :
    b.descFactorial s * a ^ s ≤ a.descFactorial s * b ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    by_cases hsb : s ≤ b
    · have hsa : s ≤ a := hsb.trans hba
      have hfactor : (b - s) * a ≤ (a - s) * b := by
        have hb := Nat.sub_add_cancel hsb
        have ha := Nat.sub_add_cancel hsa
        nlinarith
      calc
        _ = (b.descFactorial s * a ^ s) * ((b - s) * a) := by
          rw [Nat.descFactorial_succ, pow_succ]; ring
        _ ≤ (a.descFactorial s * b ^ s) * ((a - s) * b) := Nat.mul_le_mul ih hfactor
        _ = _ := by rw [Nat.descFactorial_succ, pow_succ]; ring
    · have hz : b.descFactorial (s + 1) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz, zero_mul]
      exact Nat.zero_le _

theorem choose_mul_pow_le (a b s : ℕ) (hba : b ≤ a) :
    (b.choose s : ℝ) * (a : ℝ) ^ s ≤ (a.choose s : ℝ) * (b : ℝ) ^ s := by
  have h := descFactorial_mul_pow_le a b s hba
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have hh : (s.factorial : ℝ) * ((b.choose s : ℝ) * (a : ℝ) ^ s) ≤
      (s.factorial : ℝ) * ((a.choose s : ℝ) * (b : ℝ) ^ s) := by
    rw [← mul_assoc, ← mul_assoc]
    exact_mod_cast h
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < s.factorial)).mp hh

theorem linear_weight_le_of_binomial_weight_le {a b s : ℕ} (hba : b ≤ a)
    (hsb : s ≤ b) (hs : 0 < s) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : (a.choose s : ℝ) * u ^ s ≤ (b.choose s : ℝ) * v ^ s) :
    (a : ℝ) * u ≤ (b : ℝ) * v := by
  have hb : (0 : ℝ) < b.choose s := Nat.cast_pos.mpr (Nat.choose_pos hsb)
  have hn := choose_mul_pow_le a b s hba
  have h1 := mul_le_mul_of_nonneg_right hn (pow_nonneg hu s)
  have h2 := mul_le_mul_of_nonneg_right h (pow_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) s)
  have hpow : ((a : ℝ) * u) ^ s ≤ ((b : ℝ) * v) ^ s := by
    have hprod : (b.choose s : ℝ) * (((a : ℝ) * u) ^ s - ((b : ℝ) * v) ^ s) ≤ 0 := by
      rw [mul_pow, mul_pow]
      nlinarith [h1, h2]
    nlinarith
  exact (pow_le_pow_iff_left₀ (mul_nonneg (Nat.cast_nonneg a) hu)
    (mul_nonneg (Nat.cast_nonneg b) hv) hs.ne').mp hpow

theorem weighted_rpow_le_of_linear {A B u v p : ℝ}
    (hB : 0 < B) (hBA : B ≤ A) (hu : 0 < u) (hv : 0 < v)
    (hp : 1 ≤ p) (h : A * u ≤ B * v) : A * u ^ p ≤ B * v ^ p := by
  have huv : u ≤ v := by nlinarith
  have hpow : u ^ (p - 1) ≤ v ^ (p - 1) := Real.rpow_le_rpow hu.le huv (by linarith)
  have hf (z : ℝ) (hz : 0 < z) : z ^ p = z * z ^ (p - 1) := by
    calc
      _ = z ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hz, Real.rpow_one]; ring
  rw [hf u hu, hf v hv, ← mul_assoc, ← mul_assoc]
  exact mul_le_mul h hpow (Real.rpow_nonneg hu.le _) (mul_nonneg hB.le hv.le)

universe w
variable {V : Type w} [DecidableEq V] [Fintype V] [Nonempty V]

theorem IsExtremalColoring.local_mass_ratio {r k : ℕ} {p : ℝ}
    {c : V → Fin k} (hc : IsExtremalColoring r p c) (hr : 3 ≤ r)
    (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V)
    (hQ : (RGraph.completeOfColoring r c).edges.Nonempty)
    {x : V → ℝ} (hx : (RGraph.completeOfColoring r c).IsMaximizer p x)
    {u v : V} (hsize : classSize c (c v) + 2 ≤ classSize c (c u)) :
    ((classSize c (c u) - 1 : ℕ) : ℝ) * (x u) ^ p ≤
      (classSize c (c v) : ℝ) * (x v) ^ p := by
  have huv : c u ≠ c v := by intro h; rw [h] at hsize; omega
  have hmin := hc.classSize_lower hr hp hn hQ (c v)
  have hbin := hc.binomial_weight_le hr hp hQ hx huv
  have hxpos := RGraph.complete_maximizer_pos hr c hp hQ hx
  have hlin := linear_weight_le_of_binomial_weight_le (by omega) hmin
    (show 0 < r - 1 by omega) (hxpos u).le (hxpos v).le hbin
  apply weighted_rpow_le_of_linear _ _ (hxpos u) (hxpos v) hp hlin
  · exact Nat.cast_pos.mpr (by omega)
  · exact_mod_cast (show classSize c (c v) ≤ classSize c (c u) - 1 by omega)

end ChromaticSpectral
