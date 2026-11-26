module

public import ChromaticSpectral.SymmetricMean
public import ChromaticSpectral.Averaging

/-! # The numerical inequality locating the two class-size masses

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem localization_coefficient_certificate {Q M D A B C Z : ℝ}
    (hQ : Q = M + D - 1) (hQ0 : Q ≠ 0) (hD : D ≠ 0) (hD1 : D + 1 ≠ 0)
    (hA : D * A = Q * B) (hC : (D + 1) * C = (M - 1) * A)
    (hZ : M * Z = (Q - M) * B) :
    A / Q + (1 - 1 / Q ^ 2) * C + M / Q * Z - B =
      B * (M - 1) ^ 2 * (2 * D + M - 1) / (Q * D * (D + 1)) := by
  have ha : A = Q * B / D := by apply (eq_div_iff hD).mpr; nlinarith only [hA]
  have hc : C = (M - 1) * (Q * B / D) / (D + 1) := by
    apply (eq_div_iff hD1).mpr
    rw [← ha]
    nlinarith only [hC]
  rw [show M / Q * Z = (M * Z) / Q by ring, hZ, ha, hc]
  field_simp
  rw [hQ]
  ring

/-- The binomial inequality in display (6.4), with all boundary cases included. -/
theorem localization_binomial_inequality (q m : ℕ) (hm : 2 ≤ m) (hmq : m ≤ q) :
    (q.choose (m - 1) : ℝ) / q + (1 - 1 / (q : ℝ) ^ 2) * (q.choose (m - 2) : ℝ) +
      (m : ℝ) / q * ((q - 1).choose m : ℝ) ≥ ((q - 1).choose (m - 1) : ℝ) := by
  have hq : 0 < q := by omega
  have hm1 : m - 1 + 1 = m := by omega
  have hm2 : m - 2 + 1 = m - 1 := by omega
  have hq1 : q - 1 + 1 = q := by omega
  let Q : ℝ := q
  let M : ℝ := m
  let D : ℝ := (q : ℝ) - m + 1
  let A : ℝ := q.choose (m - 1)
  let B : ℝ := (q - 1).choose (m - 1)
  let C : ℝ := q.choose (m - 2)
  let Z : ℝ := (q - 1).choose m
  have hQ : Q = M + D - 1 := by dsimp [Q, M, D]; ring
  have hQpos : 0 < Q := by dsimp [Q]; exact_mod_cast hq
  have hDpos : 0 < D := by
    dsimp [D]
    have hh : (m : ℝ) ≤ q := by exact_mod_cast hmq
    linarith
  have hM : (2 : ℝ) ≤ M := by dsimp [M]; exact_mod_cast hm
  have hA : D * A = Q * B := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_succ_eq (q - 1) (m - 1))
    rw [hq1] at hh
    push_cast at hh
    rw [Nat.cast_sub (by omega : m - 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ m)] at hh
    norm_num only [Nat.cast_one] at hh
    dsimp [D, A, Q, B]
    nlinarith only [hh]
  have hC : (D + 1) * C = (M - 1) * A := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq q (m - 2))
    rw [hm2] at hh
    push_cast at hh
    rw [Nat.cast_sub (by omega : m - 2 ≤ q), Nat.cast_sub hm,
      Nat.cast_sub (by omega : 1 ≤ m)] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [D, C, M, A]
    nlinarith only [hh]
  have hZ : M * Z = (Q - M) * B := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq (q - 1) (m - 1))
    rw [hm1] at hh
    push_cast at hh
    rw [Nat.cast_sub (by omega : m - 1 ≤ q - 1),
      Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ m)] at hh
    norm_num only [Nat.cast_one] at hh
    dsimp [M, Z, Q, B]
    nlinarith only [hh]
  have he := localization_coefficient_certificate hQ hQpos.ne' hDpos.ne'
    (by linarith : D + 1 ≠ 0) hA hC hZ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrhs : 0 ≤ B * (M - 1) ^ 2 * (2 * D + M - 1) / (Q * D * (D + 1)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hB (sq_nonneg _)) (by linarith)
    · positivity
  change B ≤ A / Q + (1 - 1 / Q ^ 2) * C + M / Q * Z
  linarith

/-- At the equal-class-mass ratio, the derivative numerator is nonnegative. -/
theorem localization_polynomial_at_rho_nonneg (q m : ℕ) (hm : 2 ≤ m) (hmq : m ≤ q) :
    0 ≤ (((q : ℝ) + 1) / q - 1) *
        ((q.choose (m - 1) : ℝ) + (q - 1 : ℕ) * (q.choose (m - 2) : ℝ) * (((q : ℝ) + 1) / q)) +
      ((q - 1).choose m : ℝ) * (((q : ℝ) + 1) / q) ^ m - (q.choose m : ℝ) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hrho : ((q : ℝ) + 1) / q = 1 + 1 / q := by field_simp
  have hb := one_add_mul_le_pow (a := (1 / (q : ℝ)))
    (le_trans (by norm_num : (-2 : ℝ) ≤ 0) (by positivity)) m
  rw [← hrho] at hb
  have hpow := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (q - 1).choose m)
  have hbin := localization_binomial_inequality q m hm hmq
  have hpas : (q.choose m : ℝ) = ((q - 1).choose (m - 1) : ℝ) + ((q - 1).choose m : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_succ' (q - 1) (m - 1))
    simpa only [show q - 1 + 1 = q by omega, show m - 1 + 1 = m by omega, Nat.cast_add] using h
  have he : (((q : ℝ) + 1) / q - 1) *
        ((q.choose (m - 1) : ℝ) + (q - 1 : ℕ) * (q.choose (m - 2) : ℝ) * (((q : ℝ) + 1) / q)) =
      (q.choose (m - 1) : ℝ) / q + (1 - 1 / (q : ℝ) ^ 2) * (q.choose (m - 2) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num only [Nat.cast_one]
    field_simp
    ring
  rw [he, hpas]
  have hpow' : ((q - 1).choose m : ℝ) +
      (m : ℝ) / q * ((q - 1).choose m : ℝ) ≤
      ((q - 1).choose m : ℝ) * (((q : ℝ) + 1) / q) ^ m := by
    convert hpow using 1 <;> ring
  linarith only [hpow', hbin]

/-- Beyond the equal-class-mass ratio, the two-class derivative has strict sign. -/
theorem localization_polynomial_pos (q m : ℕ) (hm : 2 ≤ m) (hmq : m ≤ q)
    {R : ℝ} (hR : ((q : ℝ) + 1) / q < R) :
    0 < (R - 1) *
        ((q.choose (m - 1) : ℝ) + (q - 1 : ℕ) * (q.choose (m - 2) : ℝ) * R) +
      ((q - 1).choose m : ℝ) * R ^ m - (q.choose m : ℝ) := by
  let ρ : ℝ := ((q : ℝ) + 1) / q
  let A : ℝ := q.choose (m - 1)
  let C : ℝ := (q - 1 : ℕ) * (q.choose (m - 2) : ℝ)
  let Z : ℝ := (q - 1).choose m
  have hq : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hρ : 1 ≤ ρ := by dsimp [ρ]; exact (le_div_iff₀ hq).mpr (by linarith)
  have hρR : ρ < R := hR
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.choose_pos (by omega : m - 1 ≤ q)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hT : 0 < A + C * ρ := add_pos_of_pos_of_nonneg hA (mul_nonneg hC (by linarith))
  have hTmono : A + C * ρ ≤ A + C * R := by nlinarith only [hC, hρR]
  have hstrict : (ρ - 1) * (A + C * ρ) < (R - 1) * (A + C * R) := by
    calc
      _ < (R - 1) * (A + C * ρ) := mul_lt_mul_of_pos_right (by linarith) hT
      _ ≤ _ := mul_le_mul_of_nonneg_left hTmono (by linarith)
  have hpow := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0 ≤ ρ) hρR.le m) hZ
  have hbase := localization_polynomial_at_rho_nonneg q m hm hmq
  change 0 ≤ (ρ - 1) * (A + C * ρ) + Z * ρ ^ m - (q.choose m : ℝ) at hbase
  change 0 < (R - 1) * (A + C * R) + Z * R ^ m - (q.choose m : ℝ)
  linarith only [hstrict, hpow, hbase]

/-- The stationarity equation and the two elementary layers force the mass-ratio bound. -/
theorem localization_ratio_le (q m : ℕ) (hm : 2 ≤ m) (hmq : m ≤ q)
    {a b S : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hS : (q.choose (m - 1) : ℝ) * a ^ (m - 1) +
      (q - 1 : ℕ) * (q.choose (m - 2) : ℝ) * a ^ (m - 2) * b ≤ S)
    (hstationary : (b - a) * S =
      (q.choose m : ℝ) * a ^ m - ((q - 1).choose m : ℝ) * b ^ m) :
    b ≤ (((q : ℝ) + 1) / q) * a := by
  by_contra hnot
  have hR : ((q : ℝ) + 1) / q < b / a :=
    (lt_div_iff₀ ha).mpr (lt_of_not_ge hnot)
  have hpoly := localization_polynomial_pos q m hm hmq hR
  have hscale := mul_pos (pow_pos ha m) hpoly
  have hb : b = a * (b / a) := by field_simp
  have hhom :
      (b - a) * ((q.choose (m - 1) : ℝ) * a ^ (m - 1) +
        (q - 1 : ℕ) * (q.choose (m - 2) : ℝ) * a ^ (m - 2) * b) +
        ((q - 1).choose m : ℝ) * b ^ m - (q.choose m : ℝ) * a ^ m =
      a ^ m * ((b / a - 1) *
        ((q.choose (m - 1) : ℝ) + (q - 1 : ℕ) * (q.choose (m - 2) : ℝ) * (b / a)) +
        ((q - 1).choose m : ℝ) * (b / a) ^ m - (q.choose m : ℝ)) := by
    have hm2 : m = (m - 2) + 2 := by omega
    have hm1 : m - 1 = (m - 2) + 1 := by omega
    conv_lhs => rw [hb]
    rw [hm1]
    conv_lhs => rw [hm2]
    conv_rhs => rw [hm2]
    simp only [Nat.add_sub_cancel, pow_add, pow_one, mul_pow]
    ring
  have hmul := mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hab)
  rw [← hhom] at hscale
  linarith only [hmul, hstationary, hscale]

/-- The all-in-one-class and the one-from-the-other-class terms are a lower bound. -/
theorem esymmOn_union_two_layers {V : Type*} [DecidableEq V] [Fintype V]
    {s t : Finset V} {x : V → ℝ} (hst : Disjoint s t)
    (hx : ∀ v ∈ s ∪ t, 0 ≤ x v) (j : ℕ) :
    esymmOn s (j + 1) x + (∑ v ∈ t, x v) * esymmOn s j x ≤
      esymmOn (s ∪ t) (j + 1) x := by
  induction t using Finset.induction with
  | empty => simp
  | @insert v t hvt ih =>
    have hvs : v ∉ s := fun h => (Finset.disjoint_left.mp hst) h (by simp)
    have hst' : Disjoint s t := hst.mono_right (Finset.subset_insert v t)
    have hx' : ∀ w ∈ s ∪ t, 0 ≤ x w := fun w hw => hx w
      (Finset.mem_union.mpr (by
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (Finset.mem_insert_of_mem hw)))
    have hrec := ih hst' hx'
    have hmono := esymmOn_mono_set (Finset.subset_union_left (s₂ := t)) hx' j
    have hv : v ∉ s ∪ t := by simp [hvs, hvt]
    have hvx : 0 ≤ x v := hx v (by simp)
    rw [Finset.union_insert, esymmOn_insert_succ hv, Finset.sum_insert hvt]
    nlinarith only [hrec, mul_le_mul_of_nonneg_left hmono hvx]

end ChromaticSpectral
