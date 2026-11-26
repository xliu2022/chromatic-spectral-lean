module

public import ChromaticSpectral.ExtremalBalanced
public import ChromaticSpectral.BalancedIsomorphism

/-! # Theorem 1.3: the unique spectral extremizer

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.

The comparison is stated for arbitrary finite vertex types of the same order.
The reference graph may be any complete weakly k-colourable hypergraph with
balanced colour classes. Equality is exactly graph isomorphism.
-/

@[expose] public section
namespace ChromaticSpectral
universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable [Fintype V] [Fintype W] {r k : ℕ}

namespace RGraph

theorem IsBalancedComplete.isIsomorphic {G : RGraph V r} {T : RGraph W r}
    (hG : G.IsBalancedComplete k) (hT : T.IsBalancedComplete k)
    (hcard : Fintype.card V = Fintype.card W) (hk : 0 < k) : G.IsIsomorphic T := by
  obtain ⟨c, hc, rfl⟩ := hG
  obtain ⟨d, hd, rfl⟩ := hT
  exact balanced_complete_isomorphic c d hc hd hcard hk

/-- The inequality in Theorem 1.3, for every real p ≥ 1. -/
theorem chromatic_spectral_bound (hr : 4 ≤ r) (hk : 2 ≤ k) {p : ℝ}
    (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V)
    (hcard : Fintype.card V = Fintype.card W)
    (G : RGraph V r) (T : RGraph W r) (hG : G.Colorable k)
    (hT : T.IsBalancedComplete k) : G.pSpectralRadius p ≤ T.pSpectralRadius p := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hn)
  obtain ⟨c, hc⟩ := hG
  obtain ⟨d, hd, hdbal⟩ := exists_extremal_balanced_coloring hr hk hp hn
  have hiso := (show (completeOfColoring r d).IsBalancedComplete k from ⟨d, hdbal, rfl⟩).isIsomorphic
    hT hcard (by omega)
  calc
    G.pSpectralRadius p ≤ (completeOfColoring r c).pSpectralRadius p :=
      pSpectralRadius_mono (by linarith) ((subgraph_complete_iff G c).mpr hc)
    _ ≤ (completeOfColoring r d).pSpectralRadius p := hd c
    _ = T.pSpectralRadius p := hiso.pSpectralRadius_eq (by linarith)

/-- The equality characterization in Theorem 1.3. In particular, the graph
cannot be a proper subgraph of its completed colouring. -/
theorem chromatic_spectral_eq_iff_isomorphic (hr : 4 ≤ r) (hk : 2 ≤ k) {p : ℝ}
    (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V)
    (hcard : Fintype.card V = Fintype.card W)
    (G : RGraph V r) (T : RGraph W r) (hG : G.Colorable k)
    (hT : T.IsBalancedComplete k) :
    G.pSpectralRadius p = T.pSpectralRadius p ↔ G.IsIsomorphic T := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hn)
  have hp0 : 0 < p := by linarith
  constructor
  · intro heq
    obtain ⟨c, hc⟩ := hG
    have hsub := (subgraph_complete_iff G c).mpr hc
    have hleft := pSpectralRadius_mono hp0 hsub
    have hright := chromatic_spectral_bound hr hk hp hn hcard (completeOfColoring r c) T
      (completeOfColoring_colorable c) hT
    have hQeq : (completeOfColoring r c).pSpectralRadius p = T.pSpectralRadius p :=
      le_antisymm hright (heq ▸ hleft)
    have hGQ : G = completeOfColoring r c := by
      by_contra hne
      have hproper : G.edges ⊂ (completeOfColoring r c).edges :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (RGraph.ext h)⟩
      have hstrict := pSpectralRadius_strictMono_complete (by omega : 3 ≤ r) c hp hproper
      rw [heq, hQeq] at hstrict
      exact lt_irrefl _ hstrict
    have hext : IsExtremalColoring r p c := by
      intro d
      exact (chromatic_spectral_bound hr hk hp hn hcard (completeOfColoring r d) T
        (completeOfColoring_colorable d) hT).trans_eq hQeq.symm
    exact (show G.IsBalancedComplete k from ⟨c, hext.balanced hr hk hp hn, hGQ⟩).isIsomorphic
      hT hcard (by omega)
  · intro hiso
    exact hiso.pSpectralRadius_eq hp0

/-- **Liu–Luo, Theorem 1.3**, including both the upper bound and its equality case. -/
theorem theorem_1_3 (hr : 4 ≤ r) (hk : 2 ≤ k) {p : ℝ}
    (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V)
    (hcard : Fintype.card V = Fintype.card W)
    (G : RGraph V r) (T : RGraph W r) (hG : G.Colorable k)
    (hT : T.IsBalancedComplete k) :
    G.pSpectralRadius p ≤ T.pSpectralRadius p ∧
      (G.pSpectralRadius p = T.pSpectralRadius p ↔ G.IsIsomorphic T) :=
  ⟨chromatic_spectral_bound hr hk hp hn hcard G T hG hT,
    chromatic_spectral_eq_iff_isomorphic hr hk hp hn hcard G T hG hT⟩

end RGraph
end ChromaticSpectral
