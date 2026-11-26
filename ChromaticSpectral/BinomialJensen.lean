module

public import ChromaticSpectral.BernsteinBound

/-!
# The sharp binomial Jensen inequality for balanced class sizes

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section

namespace ChromaticSpectral

theorem balanced_binomial_jensen_zero (r k q : ℕ) (hk : 0 < k) :
    (k : ℝ) * Ring.choose (((k * q : ℕ) : ℝ) / k) r =
      (0 : ℝ) * ((q + 1).choose r : ℝ) + ((k - 0 : ℕ) : ℝ) * (q.choose r : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : (((k * q : ℕ) : ℝ) / k) = (q : ℝ) := by push_cast; field_simp
  rw [he, realChoose_natCast]
  simp

theorem balanced_binomial_jensen_lt (r k q t : ℕ) (hr : 3 ≤ r) (hk : 0 < k)
    (hq : r - 1 ≤ q) (ht : 0 < t) (htk : t < k) :
    (k : ℝ) * Ring.choose (((k * q + t : ℕ) : ℝ) / k) r <
      (t : ℝ) * ((q + 1).choose r : ℝ) + ((k - t : ℕ) : ℝ) * (q.choose r : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hqR : (r : ℝ) - 1 ≤ q := by
    have h : (r : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast (show r ≤ q + 1 by omega)
    linarith
  have hα0 : (0 : ℝ) < (t : ℝ) / k := div_pos (by exact_mod_cast ht) hk0
  have hα1 : (t : ℝ) / k < 1 := (div_lt_one hk0).2 (by exact_mod_cast htk)
  have h := choose_convex_jensen_scaled r 0 hr (by omega) hqR hα0 hα1 hk0
  simp only [pow_zero, mul_one] at h
  have hν : (q : ℝ) + (t : ℝ) / k = (((k * q + t : ℕ) : ℝ) / k) := by
    push_cast
    field_simp
  have hbig : Ring.choose ((q : ℝ) + 1) r = ((q + 1).choose r : ℝ) := by
    rw [show (q : ℝ) + 1 = ((q + 1 : ℕ) : ℝ) by push_cast; rfl, realChoose_natCast]
  have hkt : (k : ℝ) * (1 - (t : ℝ) / k) = ((k - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub htk.le]
    field_simp
  have ht' : (k : ℝ) * ((t : ℝ) / k) = t := by field_simp
  rw [hν, hbig, realChoose_natCast, hkt, ht'] at h
  exact h

theorem balanced_binomial_jensen_le (r k q t : ℕ) (hr : 3 ≤ r) (hk : 0 < k)
    (hq : r - 1 ≤ q) (htk : t < k) :
    (k : ℝ) * Ring.choose (((k * q + t : ℕ) : ℝ) / k) r ≤
      (t : ℝ) * ((q + 1).choose r : ℝ) + ((k - t : ℕ) : ℝ) * (q.choose r : ℝ) := by
  by_cases ht : t = 0
  · subst t
    simpa only [Nat.add_zero, Nat.cast_zero] using (balanced_binomial_jensen_zero r k q hk).le
  · exact (balanced_binomial_jensen_lt r k q t hr hk hq (Nat.pos_of_ne_zero ht) htk).le

theorem balanced_binomial_jensen_eq_iff (r k q t : ℕ) (hr : 3 ≤ r) (hk : 0 < k)
    (hq : r - 1 ≤ q) (htk : t < k) :
    (k : ℝ) * Ring.choose (((k * q + t : ℕ) : ℝ) / k) r =
        (t : ℝ) * ((q + 1).choose r : ℝ) + ((k - t : ℕ) : ℝ) * (q.choose r : ℝ) ↔
      t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact (balanced_binomial_jensen_lt r k q t hr hk hq (Nat.pos_of_ne_zero ht) htk).ne h
  · rintro rfl
    simpa only [Nat.add_zero, Nat.cast_zero] using balanced_binomial_jensen_zero r k q hk

end ChromaticSpectral
