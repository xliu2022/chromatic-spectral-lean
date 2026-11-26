module

public import ChromaticSpectral.ElementarySymmetric

/-! # Two-coordinate identities and symmetric-mean deficits

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

variable {V : Type*} [DecidableEq V]

theorem esymmOn_two_insert {s : Finset V} {u v : V}
    (hu : u ∉ s) (hv : v ∉ s) (hne : u ≠ v) (j : ℕ) (x : V → ℝ) :
    esymmOn (insert u (insert v s)) (j + 2) x =
      esymmOn s (j + 2) x + (x u + x v) * esymmOn s (j + 1) x +
        x u * x v * esymmOn s j x := by
  have hui : u ∉ insert v s := by simp [hu, hne]
  rw [show j + 2 = (j + 1) + 1 by omega, esymmOn_insert_succ hui,
    esymmOn_insert_succ hv, esymmOn_insert_succ hv]
  ring

theorem esymmOn_two_erase {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (j : ℕ) (x : V → ℝ) :
    esymmOn s (j + 2) x =
      esymmOn ((s.erase u).erase v) (j + 2) x +
        (x u + x v) * esymmOn ((s.erase u).erase v) (j + 1) x +
        x u * x v * esymmOn ((s.erase u).erase v) j x := by
  have he : insert u (insert v ((s.erase u).erase v)) = s := by
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hne.symm, hv⟩), Finset.insert_erase hu]
  have hu' : u ∉ (s.erase u).erase v := by simp
  have hv' : v ∉ (s.erase u).erase v := by simp
  simpa only [he] using esymmOn_two_insert hu' hv' hne j x

theorem sum_pair_covariance (s : Finset V) (x f : V → ℝ) :
    ∑ u ∈ s, ∑ v ∈ s, (x u - x v) * (f v - f u) =
      2 * ((∑ u ∈ s, x u) * (∑ u ∈ s, f u) -
        (s.card : ℝ) * ∑ u ∈ s, x u * f u) := by
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
  have hc : (∑ i ∈ s, x i * ((s.card : ℝ) * f i)) =
      (s.card : ℝ) * ∑ i ∈ s, x i * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc, ← Finset.mul_sum]
  ring

/-- Twice the adjacent symmetric-mean deficit is the ordered sum of squared
coordinate differences. The diagonal terms vanish. -/
theorem two_mul_esymmOn_gap_eq_sum_pairs (s : Finset V) (j : ℕ) (x : V → ℝ) :
    2 * (((s.card : ℝ) - (j + 1)) * esymmOn s 1 x * esymmOn s (j + 1) x -
      (s.card : ℝ) * (j + 2) * esymmOn s (j + 2) x) =
      ∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 * esymmOn ((s.erase u).erase v) j x := by
  have hp : (∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 *
      esymmOn ((s.erase u).erase v) j x) =
      ∑ u ∈ s, ∑ v ∈ s, (x u - x v) *
        (esymmOn (s.erase v) (j + 1) x - esymmOn (s.erase u) (j + 1) x) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases huv : u = v
    · subst v; simp
    · have he := esymmOn_erase_sub hu hv huv j x
      linear_combination (x u - x v) * he
  rw [hp, sum_pair_covariance, sum_esymmOn_erase, sum_mul_esymmOn_erase, ← esymmOn_one]
  push_cast
  ring

/-- Replace two distinct coordinates, keeping all other coordinates fixed. -/
def twoUpdate (x : V → ℝ) (u v : V) (a b : ℝ) : V → ℝ :=
  Function.update (Function.update x u a) v b

theorem twoUpdate_apply_left (x : V → ℝ) {u v : V} (hne : u ≠ v) (a b : ℝ) :
    twoUpdate x u v a b u = a := by simp [twoUpdate, hne]

@[simp] theorem twoUpdate_apply_right (x : V → ℝ) (u v : V) (a b : ℝ) :
    twoUpdate x u v a b v = b := by simp [twoUpdate]

theorem twoUpdate_apply_of_ne (x : V → ℝ) {u v w : V}
    (hwu : w ≠ u) (hwv : w ≠ v) (a b : ℝ) :
    twoUpdate x u v a b w = x w := by simp [twoUpdate, hwu, hwv]

theorem esymmOn_twoUpdate_rest (s : Finset V) (x : V → ℝ) (u v : V)
    (a b : ℝ) (j : ℕ) :
    esymmOn ((s.erase u).erase v) j (twoUpdate x u v a b) =
      esymmOn ((s.erase u).erase v) j x := by
  apply esymmOn_congr
  intro w hw
  exact twoUpdate_apply_of_ne x (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    (Finset.mem_erase.mp hw).1 a b

theorem esymmOn_twoUpdate_sub {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (j : ℕ) (x : V → ℝ) (a b : ℝ) :
    esymmOn s (j + 2) (twoUpdate x u v a b) - esymmOn s (j + 2) x =
      (a + b - (x u + x v)) * esymmOn ((s.erase u).erase v) (j + 1) x +
        (a * b - x u * x v) * esymmOn ((s.erase u).erase v) j x := by
  rw [esymmOn_two_erase hu hv hne j (twoUpdate x u v a b),
    esymmOn_two_erase hu hv hne j x]
  simp only [esymmOn_twoUpdate_rest, twoUpdate_apply_left x hne, twoUpdate_apply_right]
  ring

noncomputable def pairAverage (x : V → ℝ) (u v : V) : V → ℝ :=
  twoUpdate x u v ((x u + x v) / 2) ((x u + x v) / 2)

theorem esymmOn_pairAverage_sub {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (j : ℕ) (x : V → ℝ) :
    esymmOn s (j + 2) (pairAverage x u v) - esymmOn s (j + 2) x =
      (x u - x v) ^ 2 / 4 * esymmOn ((s.erase u).erase v) j x := by
  rw [pairAverage, esymmOn_twoUpdate_sub hu hv hne]
  ring

theorem sum_pair_sq (s : Finset V) (x : V → ℝ) :
    ∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 =
      2 * ((s.card : ℝ) * (∑ u ∈ s, (x u) ^ 2) - (∑ u ∈ s, x u) ^ 2) := by
  have h := sum_pair_covariance s x x
  have he (u v : V) : (x u - x v) * (x v - x u) = -(x u - x v) ^ 2 := by ring
  simp_rw [he, Finset.sum_neg_distrib, ← sq] at h
  linarith

theorem sum_sq_sub (s : Finset V) (x : V → ℝ) (c : ℝ) :
    ∑ v ∈ s, (x v - c) ^ 2 =
      (∑ v ∈ s, (x v) ^ 2) - 2 * c * (∑ v ∈ s, x v) + (s.card : ℝ) * c ^ 2 := by
  have he (v : V) : (x v - c) ^ 2 = (x v) ^ 2 - 2 * c * x v + c ^ 2 := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem sum_pair_sq_eq_variance {s : Finset V} {x : V → ℝ} {c : ℝ}
    (hc : ∑ v ∈ s, x v = (s.card : ℝ) * c) :
    ∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 =
      2 * (s.card : ℝ) * ∑ v ∈ s, (x v - c) ^ 2 := by
  rw [sum_pair_sq, sum_sq_sub, hc]
  ring

/-- A finite algebraic lower bound for the adjacent symmetric-mean deficit.
It is the quantitative input for Claim 6.6 and uses no limiting averaging process. -/
theorem esymmOn_gap_ge_variance {s : Finset V} {x : V → ℝ} {m c : ℝ}
    (hm : 0 ≤ m) (hx : ∀ v ∈ s, m ≤ x v)
    (hc : ∑ v ∈ s, x v = (s.card : ℝ) * c) (j : ℕ) :
    (s.card : ℝ) * ((s.card - 2).choose j : ℝ) * m ^ j *
        (∑ v ∈ s, (x v - c) ^ 2) ≤
      ((s.card : ℝ) - (j + 1)) * esymmOn s 1 x * esymmOn s (j + 1) x -
        (s.card : ℝ) * (j + 2) * esymmOn s (j + 2) x := by
  let C : ℝ := ((s.card - 2).choose j : ℝ) * m ^ j
  have hpair : ∀ u ∈ s, ∀ v ∈ s,
      C * (x u - x v) ^ 2 ≤
        (x u - x v) ^ 2 * esymmOn ((s.erase u).erase v) j x := by
    intro u hu v hv
    by_cases huv : u = v
    · subst v; simp
    have hv' : v ∈ s.erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩
    have hcard : ((s.erase u).erase v).card = s.card - 2 := by
      rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu]
      omega
    have he := esymmOn_mono (s := (s.erase u).erase v) (x := fun _ => m)
      (fun _ _ => hm)
      (fun w hw => hx w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))) j
    rw [esymmOn_const, hcard] at he
    have h := mul_le_mul_of_nonneg_left he (sq_nonneg (x u - x v))
    simpa only [C, mul_comm C] using h
  have hb := Finset.sum_le_sum fun u hu => Finset.sum_le_sum (hpair u hu)
  simp_rw [← Finset.mul_sum] at hb
  rw [sum_pair_sq_eq_variance hc] at hb
  have he := two_mul_esymmOn_gap_eq_sum_pairs s j x
  rw [← he] at hb
  dsimp [C] at hb
  nlinarith [hb]

theorem sum_twoUpdate {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (x : V → ℝ) (a b : ℝ) :
    (∑ w ∈ s, twoUpdate x u v a b w) = (∑ w ∈ s, x w) + (a + b - (x u + x v)) := by
  have hv' : v ∈ s.erase u := Finset.mem_erase.mpr ⟨hne.symm, hv⟩
  have h1 := esymmOn_erase_succ hu 0 x
  have h2 := esymmOn_erase_succ hv' 0 x
  have h3 := esymmOn_erase_succ hu 0 (twoUpdate x u v a b)
  have h4 := esymmOn_erase_succ hv' 0 (twoUpdate x u v a b)
  rw [esymmOn_twoUpdate_rest] at h4
  simp only [zero_add, esymmOn_zero, mul_one, esymmOn_one,
    twoUpdate_apply_left x hne, twoUpdate_apply_right] at h1 h2 h3 h4
  linarith

theorem esymmOn_twoUpdate_le_of_sum_prod {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) {x : V → ℝ} {a b : ℝ}
    (hx : ∀ w ∈ s, 0 ≤ x w) (hsum : a + b ≤ x u + x v)
    (hprod : a * b ≤ x u * x v) (j : ℕ) :
    esymmOn s j (twoUpdate x u v a b) ≤ esymmOn s j x := by
  cases j with
  | zero => simp
  | succ j =>
      cases j with
      | zero => simp only [Nat.zero_add, esymmOn_one, sum_twoUpdate hu hv hne]; linarith
      | succ j =>
          have he := esymmOn_twoUpdate_sub hu hv hne j x a b
          have hn (d : ℕ) : 0 ≤ esymmOn ((s.erase u).erase v) d x :=
            esymmOn_nonneg (fun w hw => hx w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))) d
          have h1 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsum) (hn (j + 1))
          have h2 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hprod) (hn j)
          linarith

/-- Concavity gives the two-coordinate reverse smoothing inequality for real powers. -/
theorem pair_rpow_sum_ge {a b x y θ : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) (hay : a ≤ y) (hxb : x ≤ b) (hyb : y ≤ b)
    (hs : a + b = x + y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    a ^ θ + b ^ θ ≤ x ^ θ + y ^ θ := by
  by_cases hab : a = b
  · have hx : x = a := by linarith
    have hy : y = a := by linarith
    simp [hab, hx, hy]
  have hab' : a < b := lt_of_le_of_ne (hax.trans hxb) hab
  let α : ℝ := (b - x) / (b - a)
  let β : ℝ := (x - a) / (b - a)
  have hd : 0 < b - a := sub_pos.mpr hab'
  have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hxb) hd.le
  have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hax) hd.le
  have hw : α + β = 1 := by dsimp [α, β]; field_simp; ring
  have hx' : α * a + β * b = x := by dsimp [α, β]; field_simp; ring
  have hy' : β * a + α * b = y := by
    have hh : (α * a + β * b) + (β * a + α * b) = a + b := by
      calc
        _ = (α + β) * (a + b) := by ring
        _ = _ := by rw [hw, one_mul]
    linarith
  have hcon := Real.concaveOn_rpow hθ0 hθ1
  have h1 := hcon.2 ha (ha.trans (hax.trans hxb)) hα hβ hw
  have h2 := hcon.2 ha (ha.trans (hax.trans hxb)) hβ hα (by linarith)
  simp only [smul_eq_mul, hx', hy'] at h1 h2
  have hh : (α * a ^ θ + β * b ^ θ) + (β * a ^ θ + α * b ^ θ) = a ^ θ + b ^ θ := by
    calc
      _ = (α + β) * (a ^ θ + b ^ θ) := by ring
      _ = _ := by rw [hw, one_mul]
  linarith

theorem rpow_twoUpdate (x : V → ℝ) (u v : V) (a b θ : ℝ) :
    (fun w => (twoUpdate x u v a b w) ^ θ) =
      twoUpdate (fun w => (x w) ^ θ) u v (a ^ θ) (b ^ θ) := by
  funext w
  by_cases hv : w = v
  · subst w; simp [twoUpdate]
  by_cases hu : w = u
  · subst w; simp [twoUpdate, hv]
  simp [twoUpdate, hu, hv]

theorem esymmOn_rpow_twoUpdate_le {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) {x : V → ℝ} {a b θ : ℝ}
    (hx : ∀ w ∈ s, 0 ≤ x w) (ha : 0 ≤ a)
    (hau : a ≤ x u) (hav : a ≤ x v) (hub : x u ≤ b) (hvb : x v ≤ b)
    (hs : a + b = x u + x v) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : ℕ) :
    esymmOn s j (fun w => (twoUpdate x u v a b w) ^ θ) ≤
      esymmOn s j (fun w => (x w) ^ θ) := by
  rw [rpow_twoUpdate]
  apply esymmOn_twoUpdate_le_of_sum_prod hu hv hne
    (fun w hw => Real.rpow_nonneg (hx w hw) θ)
  · exact pair_rpow_sum_ge ha hau hav hub hvb hs hθ0 hθ1
  · have hp : a * b ≤ x u * x v := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hau) (sub_nonneg.mpr hav)]
    have h := Real.rpow_le_rpow (mul_nonneg ha (ha.trans (hau.trans hub))) hp hθ0
    simpa only [Real.mul_rpow ha (ha.trans (hau.trans hub)), Real.mul_rpow (hx u hu) (hx v hv)] using h

end ChromaticSpectral
