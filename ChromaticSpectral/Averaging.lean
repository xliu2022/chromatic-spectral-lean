module

public import ChromaticSpectral.TwoCoordinate
public import ChromaticSpectral.Normalization
public import ChromaticSpectral.CompletePolynomial

/-! # Pair averaging in nonnegative p-balls
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

theorem sum_comp_twoUpdate (g : ℝ → ℝ) (x : V → ℝ) {u v : V}
    (hne : u ≠ v) (a b : ℝ) :
    ∑ w, g (twoUpdate x u v a b w) =
      (∑ w, g (x w)) + (g a - g (x u)) + (g b - g (x v)) := by
  have hpoint : ∀ w, g (twoUpdate x u v a b w) = g (x w) +
      (if w = u then g a - g (x u) else 0) +
      (if w = v then g b - g (x v) else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp [twoUpdate, hne]
    · by_cases hwv : w = v
      · subst w
        simp [twoUpdate, hne.symm]
      · simp [twoUpdate, hwu, hwv]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp

theorem pairAverage_nonneg {x : V → ℝ} (hx : ∀ w, 0 ≤ x w) (u v : V) :
    ∀ w, 0 ≤ pairAverage x u v w := by
  intro w
  simp only [pairAverage, twoUpdate, Function.update_apply]
  split_ifs <;> first
    | exact div_nonneg (add_nonneg (hx u) (hx v)) (by norm_num)
    | exact hx _

theorem two_mul_rpow_midpoint_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 ≤ p) : 2 * ((a + b) / 2) ^ p ≤ a ^ p + b ^ p := by
  have h := (convexOn_rpow hp).2 ha hb
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  rw [he] at h
  linarith

theorem pairAverage_mass_le {x : V → ℝ} {p : ℝ} (hx : ∀ w, 0 ≤ x w)
    (hp : 1 ≤ p) {u v : V} (hne : u ≠ v) :
    ∑ w, (pairAverage x u v w) ^ p ≤ ∑ w, (x w) ^ p := by
  rw [pairAverage, sum_comp_twoUpdate (fun t => t ^ p) x hne]
  have h := two_mul_rpow_midpoint_le (hx u) (hx v) hp
  linarith

theorem esymmOn_mono_set {s t : Finset V} (hst : s ⊆ t) {x : V → ℝ}
    (hx : ∀ v ∈ t, 0 ≤ x v) (j : ℕ) : esymmOn s j x ≤ esymmOn t j x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨hes, hec⟩ := Finset.mem_powersetCard.mp he
    exact Finset.mem_powersetCard.mpr ⟨hes.trans hst, hec⟩
  · intro e he _
    exact Finset.prod_nonneg fun v hv => hx v ((Finset.mem_powersetCard.mp he).1 hv)

theorem esymmOn_strictMono_set {s t e : Finset V} (hst : s ⊆ t)
    {x : V → ℝ} (hx : ∀ v ∈ t, 0 ≤ x v) {j : ℕ}
    (het : e ⊆ t) (hec : e.card = j) (hes : ¬ e ⊆ s)
    (hprod : 0 < ∏ v ∈ e, x v) : esymmOn s j x < esymmOn t j x := by
  apply Finset.sum_lt_sum_of_subset
    (s := s.powersetCard j) (t := t.powersetCard j) (i := e)
  · intro f hf
    obtain ⟨hfs, hfc⟩ := Finset.mem_powersetCard.mp hf
    exact Finset.mem_powersetCard.mpr ⟨hfs.trans hst, hfc⟩
  · exact Finset.mem_powersetCard.mpr ⟨het, hec⟩
  · exact fun h => hes (Finset.mem_powersetCard.mp h).1
  · exact hprod
  · intro f hf _
    exact Finset.prod_nonneg fun v hv => hx v ((Finset.mem_powersetCard.mp hf).1 hv)

end ChromaticSpectral
