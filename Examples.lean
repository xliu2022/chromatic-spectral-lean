module

import ChromaticSpectral

/-! # Examples of applying the formalized main theorems
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

open ChromaticSpectral

example {n r k : ℕ} {p : ℝ} (G T : RGraph (Fin n) r)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hp : 1 ≤ p) (hn : (r - 1) * k < n)
    (hG : G.Colorable k) (hT : T.IsBalancedComplete k) :
    G.pSpectralRadius p ≤ T.pSpectralRadius p ∧
      (G.pSpectralRadius p = T.pSpectralRadius p ↔ G.IsIsomorphic T) := by
  exact theorem_1_3 hr hk hp (by simpa using hn) rfl G T hG hT

example {n r k : ℕ} {p : ℝ} (G : RGraph (Fin n) r)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hp : 1 ≤ p) (hn : (r - 1) * k < n)
    (hG : G.Colorable k) :
    G.pSpectralRadius p ≤ explicitBound r k n p := by
  simpa using chromatic_explicit_bound G hG hr hk (by simpa using hn) hp

example :
    (RGraph.completeOfColoring 4 SemanticChecks.twoClassesOfFour).pSpectralRadius 1 = 51 / 128 := by
  have h := (theorem_1_4
    (RGraph.completeOfColoring 4 SemanticChecks.twoClassesOfFour)
    ⟨SemanticChecks.twoClassesOfFour, SemanticChecks.twoClassesOfFour_balanced, rfl⟩
    (by decide) (by decide) (by decide) (by norm_num : (1 : ℝ) ≤ 1)).2.mpr (by decide)
  exact h.trans SemanticChecks.explicitBound_divisible_lagrangian
