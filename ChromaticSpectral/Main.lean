module

public import ChromaticSpectral.Theorem13
public import ChromaticSpectral.ExplicitTheorem

/-! # Main results and the spectral colouring criterion

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.

This is the public entry point for Theorems 1.3 and 1.4, the combined explicit
bound with its equality characterization, and Corollary 1.5.
-/

@[expose] public section
namespace ChromaticSpectral

export RGraph (theorem_1_3)

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable [Fintype V] [Fintype W] {r k : ℕ}

/-- The reference balanced complete graph exists throughout the main range. -/
theorem exists_balanced_complete (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hn : (r - 1) * k < Fintype.card V) :
    ∃ T : RGraph V r, T.IsBalancedComplete k := by
  let : Nonempty V := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hn)
  obtain ⟨c, _, hc⟩ := exists_extremal_balanced_coloring hr hk (p := 1) (by norm_num) hn
  exact ⟨RGraph.completeOfColoring r c, c, hc, rfl⟩

/-- The explicit bound for every weakly k-colourable r-graph. -/
theorem chromatic_explicit_bound (G : RGraph V r) (hG : G.Colorable k)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hn : (r - 1) * k < Fintype.card V)
    {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p ≤ explicitBound r k (Fintype.card V) p := by
  obtain ⟨T, hT⟩ := exists_balanced_complete hr hk hn
  exact (RGraph.chromatic_spectral_bound hr hk hp hn rfl G T hG hT).trans
    (theorem_1_4 T hT hr hk hn hp).1

/-- The combination of Theorems 1.3 and 1.4, including the exact equality case
in the explicit bound (Conjecture 1.2 in the paper). -/
theorem chromatic_explicit_eq_iff (G : RGraph V r) (T : RGraph W r)
    (hG : G.Colorable k) (hT : T.IsBalancedComplete k)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hn : (r - 1) * k < Fintype.card V)
    (hcard : Fintype.card V = Fintype.card W) {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p = explicitBound r k (Fintype.card V) p ↔
      k ∣ Fintype.card V ∧ G.IsIsomorphic T := by
  have h13 := theorem_1_3 hr hk hp hn hcard G T hG hT
  have h14 := theorem_1_4 T hT hr hk (hcard ▸ hn) hp
  rw [← hcard] at h14
  constructor
  · intro heq
    have hTval : T.pSpectralRadius p = explicitBound r k (Fintype.card V) p :=
      le_antisymm h14.1 (heq ▸ h13.1)
    exact ⟨h14.2.mp hTval, h13.2.mp (heq.trans hTval.symm)⟩
  · rintro ⟨hd, hiso⟩
    exact (h13.2.mpr hiso).trans (h14.2.mpr hd)

/-- **Liu–Luo, Corollary 1.5**: exceeding the explicit threshold rules out a
weak k-colouring. -/
theorem corollary_1_5 (G : RGraph V r) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hn : (r - 1) * k < Fintype.card V) {p : ℝ} (hp : 1 ≤ p)
    (hspectral : explicitBound r k (Fintype.card V) p < G.pSpectralRadius p) :
    ¬ G.Colorable k := by
  intro hG
  exact (not_lt_of_ge (chromatic_explicit_bound G hG hr hk hn hp)) hspectral

end ChromaticSpectral
