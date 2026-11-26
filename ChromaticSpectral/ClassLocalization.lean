module

public import ChromaticSpectral.ClassOrder
public import ChromaticSpectral.LocalizationNumerics

/-! # Localization of the two weights for adjacent class sizes

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] [Nonempty V] {r k q : ℕ}

/-- At a Lagrangian maximum, the ratio of the small-class weight to the
large-class weight is at most the ratio of the adjacent class sizes. -/
theorem RGraph.complete_maximizer_adjacent_class_ratio (hr : 4 ≤ r)
    (c : V → Fin k) (hQ : (completeOfColoring r c).edges.Nonempty)
    {x : V → ℝ} (hx : (completeOfColoring r c).IsMaximizer 1 x)
    (hq : r - 1 ≤ q) {u v : V}
    (hu : classSize c (c u) = q + 1) (hv : classSize c (c v) = q) :
    x v ≤ (((q : ℝ) + 1) / q) * x u := by
  have hr3 : 3 ≤ r := by omega
  have hc : c u ≠ c v := by intro hc; rw [hc, hv] at hu; omega
  have hpos := complete_maximizer_pos hr3 c (by norm_num) hQ hx
  have hab := complete_maximizer_weight_antitone hr3 c hQ hx
    (show classSize c (c v) ≤ classSize c (c u) by rw [hu, hv]; omega)
  have hstationary := complete_maximizer_binomial_stationarity hr3 c hQ hx hc
  rw [hu, hv, Nat.add_sub_cancel] at hstationary
  let U := (classSet c (c u)).erase u
  let T := (classSet c (c v)).erase v
  let S := (Finset.univ.erase u).erase v
  have hUcard : U.card = q := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (by simp), classSet_card, hu]
    omega
  have hTcard : T.card = q - 1 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem (by simp), classSet_card, hv]
  have hUconst : ∀ w ∈ U, x w = x u := by
    intro w hw
    exact complete_maximizer_constant_on_classes hr3 c (by norm_num) hQ hx
      ((mem_classSet c (c u) w).mp (Finset.mem_of_mem_erase hw))
  have hTconst : ∀ w ∈ T, x w = x v := by
    intro w hw
    exact complete_maximizer_constant_on_classes hr3 c (by norm_num) hQ hx
      ((mem_classSet c (c v) w).mp (Finset.mem_of_mem_erase hw))
  have hUT : Disjoint U T := by
    apply Finset.disjoint_left.mpr
    intro w hwU hwT
    have hwcu := (mem_classSet c (c u) w).mp (Finset.mem_of_mem_erase hwU)
    have hwcv := (mem_classSet c (c v) w).mp (Finset.mem_of_mem_erase hwT)
    exact hc (hwcu.symm.trans hwcv)
  have hsubset : U ∪ T ⊆ S := by
    intro w hw
    apply Finset.mem_erase.mpr
    constructor
    · rcases Finset.mem_union.mp hw with hw | hw
      · intro hwv
        have hcw := (mem_classSet c (c u) w).mp (Finset.mem_of_mem_erase hw)
        exact hc (hcw.symm.trans (congrArg c hwv))
      · exact (Finset.mem_erase.mp hw).1
    · apply Finset.mem_erase.mpr
      constructor
      · rcases Finset.mem_union.mp hw with hw | hw
        · exact (Finset.mem_erase.mp hw).1
        · intro hwu
          have hcw := (mem_classSet c (c v) w).mp (Finset.mem_of_mem_erase hw)
          exact hc ((congrArg c hwu).symm.trans hcw)
      · exact Finset.mem_univ w
  have hEU (d : ℕ) : esymmOn U d x = (q.choose d : ℝ) * (x u) ^ d := by
    rw [esymmOn_congr hUconst d, esymmOn_const, hUcard]
  have hsumT : ∑ w ∈ T, x w = (q - 1 : ℕ) * x v := by
    calc
      _ = ∑ w ∈ T, x v := Finset.sum_congr rfl hTconst
      _ = _ := by simp [hTcard]
  have hlower := esymmOn_union_two_layers hUT
    (fun w _ => (hpos w).le) (r - 3)
  rw [hEU, hEU, hsumT] at hlower
  have hmono := esymmOn_mono_set hsubset (fun w _ => (hpos w).le) (r - 2)
  have hindex : r - 3 + 1 = r - 2 := by omega
  rw [hindex] at hlower
  have hbound : (q.choose (r - 1 - 1) : ℝ) * (x u) ^ (r - 1 - 1) +
      (q - 1 : ℕ) * (q.choose (r - 1 - 2) : ℝ) * (x u) ^ (r - 1 - 2) * x v ≤
      esymmOn S (r - 1 - 1) x := by
    have hi1 : r - 1 - 1 = r - 2 := by omega
    have hi2 : r - 1 - 2 = r - 3 := by omega
    rw [hi1, hi2]
    nlinarith only [hlower, hmono]
  exact localization_ratio_le q (r - 1) (by omega) hq (hpos u) hab hbound
    (by simpa only [show r - 1 - 1 = r - 2 by omega, S] using hstationary)

end ChromaticSpectral
