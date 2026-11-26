module

public import ChromaticSpectral.Basic

/-! # A second-derivative interpolation bound

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section

namespace ChromaticSpectral

theorem interpolation_defect_le_of_hasDerivAt2 {f f' f'' : ℝ → ℝ} {q α M : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hf : ContinuousOn f (Set.Icc q (q + 1)))
    (hf' : ∀ y ∈ Set.Ioo q (q + 1), HasDerivAt f (f' y) y)
    (hf'' : ∀ y ∈ Set.Ioo q (q + 1), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Ioo q (q + 1), -M ≤ f'' y) :
    f (q + α) - (1 - α) * f q - α * f (q + 1) ≤ M / 2 * α * (1 - α) := by
  let g : ℝ → ℝ := fun y => f y + M / 2 * y ^ 2
  let g' : ℝ → ℝ := fun y => f' y + M * y
  let g'' : ℝ → ℝ := fun y => f'' y + M
  have hgc : ContinuousOn g (Set.Icc q (q + 1)) := by
    exact hf.add ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  have hg' (y : ℝ) (hy : y ∈ Set.Ioo q (q + 1)) : HasDerivAt g (g' y) y := by
    have h := (hf' y hy).add (((hasDerivAt_id y).pow 2).const_mul (M / 2))
    convert h using 1 <;> dsimp [g, g'] <;> first | rfl | ring
  have hg'' (y : ℝ) (hy : y ∈ Set.Ioo q (q + 1)) : HasDerivAt g' (g'' y) y := by
    have h := (hf'' y hy).add ((hasDerivAt_id y).const_mul M)
    convert h using 1 <;> dsimp [g', g''] <;> first | rfl | ring
  have hconv : ConvexOn ℝ (Set.Icc q (q + 1)) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g') (f'' := g'') (convex_Icc _ _) hgc
    · intro y hy
      rw [interior_Icc] at hy
      exact (hg' y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hg'' y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      dsimp [g'']
      linarith [hbound y hy]
  have hq : q ∈ Set.Icc q (q + 1) := ⟨le_rfl, by linarith⟩
  have hq1 : q + 1 ∈ Set.Icc q (q + 1) := ⟨by linarith, le_rfl⟩
  have h := hconv.2 hq hq1 (sub_nonneg.mpr hα1) hα0 (by ring : (1 - α) + α = 1)
  have he : (1 - α) * q + α * (q + 1) = q + α := by ring
  simp only [smul_eq_mul, he, g] at h
  nlinarith only [h]

theorem interpolation_defect_le {f : ℝ → ℝ} {q α M : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hf : ContinuousOn f (Set.Icc q (q + 1)))
    (hf' : ∀ y ∈ Set.Ioo q (q + 1), DifferentiableAt ℝ f y)
    (hf'' : ∀ y ∈ Set.Ioo q (q + 1), DifferentiableAt ℝ (deriv f) y)
    (hbound : ∀ y ∈ Set.Ioo q (q + 1), -M ≤ deriv (deriv f) y) :
    f (q + α) - (1 - α) * f q - α * f (q + 1) ≤ M / 2 * α * (1 - α) :=
  interpolation_defect_le_of_hasDerivAt2 hα0 hα1 hf
    (fun y hy => (hf' y hy).hasDerivAt) (fun y hy => (hf'' y hy).hasDerivAt) hbound

end ChromaticSpectral
