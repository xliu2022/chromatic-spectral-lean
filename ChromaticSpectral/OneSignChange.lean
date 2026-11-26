module

public import ChromaticSpectral.Basic

/-!
# Finite sums whose coefficients change sign once

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.

These elementary comparison lemmas replace the uses of Descartes' rule
in Sections 4 and 5 of Liu--Luo, arXiv:2605.14755v1.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem oneSignChange_scale_le {I : Type*} (S : Finset I)
    (a : I → ℝ) (e : I → ℕ) (j : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hlo : ∀ i ∈ S, e i ≤ j → 0 ≤ a i)
    (hhi : ∀ i ∈ S, j < e i → a i ≤ 0) :
    u ^ j * (∑ i ∈ S, a i) ≤ ∑ i ∈ S, a i * u ^ e i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  by_cases he : e i ≤ j
  · simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu hu1 he) (hlo i hi he)
  · simpa [mul_comm] using
      mul_le_mul_of_nonpos_left
        (pow_le_pow_of_le_one hu hu1 (Nat.le_of_lt (Nat.lt_of_not_ge he)))
        (hhi i hi (Nat.lt_of_not_ge he))

theorem oneSignChange_scale_ge {I : Type*} (S : Finset I)
    (a : I → ℝ) (e : I → ℕ) (j : ℕ) {u : ℝ}
    (hu : 1 ≤ u)
    (hlo : ∀ i ∈ S, e i < j → a i ≤ 0)
    (hhi : ∀ i ∈ S, j ≤ e i → 0 ≤ a i) :
    u ^ j * (∑ i ∈ S, a i) ≤ ∑ i ∈ S, a i * u ^ e i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  by_cases he : j ≤ e i
  · simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu he) (hhi i hi he)
  · simpa [mul_comm] using
      mul_le_mul_of_nonpos_left
        (pow_le_pow_right₀ hu (Nat.le_of_lt (Nat.lt_of_not_ge he)))
        (hlo i hi (Nat.lt_of_not_ge he))

theorem oneSignChange_pos_below {I : Type*} (S : Finset I)
    (a : I → ℝ) (e : I → ℕ) (j : ℕ) {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hxc : x ≤ c)
    (hlo : ∀ i ∈ S, e i ≤ j → 0 ≤ a i)
    (hhi : ∀ i ∈ S, j < e i → a i ≤ 0)
    (hendpoint : 0 < ∑ i ∈ S, a i * c ^ e i) :
    0 < ∑ i ∈ S, a i * x ^ e i := by
  have hu : 0 < x / c := div_pos hx hc
  have hu1 : x / c ≤ 1 := (div_le_one hc).2 hxc
  have h := oneSignChange_scale_le S (fun i => a i * c ^ e i) e j hu.le hu1
    (fun i hi he => mul_nonneg (hlo i hi he) (pow_nonneg hc.le _))
    (fun i hi he => mul_nonpos_of_nonpos_of_nonneg (hhi i hi he)
      (pow_nonneg hc.le _))
  have hpos : 0 < (x / c) ^ j * (∑ i ∈ S, a i * c ^ e i) :=
    mul_pos (pow_pos hu _) hendpoint
  have heq : (∑ i ∈ S, a i * c ^ e i * (x / c) ^ e i) =
      ∑ i ∈ S, a i * x ^ e i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hc.ne']
  exact heq ▸ hpos.trans_le h

theorem oneSignChange_pos_above {I : Type*} (S : Finset I)
    (a : I → ℝ) (e : I → ℕ) (j : ℕ) {c x : ℝ}
    (hc : 0 < c) (hcx : c ≤ x)
    (hlo : ∀ i ∈ S, e i < j → a i ≤ 0)
    (hhi : ∀ i ∈ S, j ≤ e i → 0 ≤ a i)
    (hendpoint : 0 < ∑ i ∈ S, a i * c ^ e i) :
    0 < ∑ i ∈ S, a i * x ^ e i := by
  have hu : 1 ≤ x / c := (one_le_div hc).2 hcx
  have h := oneSignChange_scale_ge S (fun i => a i * c ^ e i) e j hu
    (fun i hi he => mul_nonpos_of_nonpos_of_nonneg (hlo i hi he)
      (pow_nonneg hc.le _))
    (fun i hi he => mul_nonneg (hhi i hi he) (pow_nonneg hc.le _))
  have hpos : 0 < (x / c) ^ j * (∑ i ∈ S, a i * c ^ e i) :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hu) _) hendpoint
  have heq : (∑ i ∈ S, a i * c ^ e i * (x / c) ^ e i) =
      ∑ i ∈ S, a i * x ^ e i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hc.ne']
  exact heq ▸ hpos.trans_le h

end ChromaticSpectral
