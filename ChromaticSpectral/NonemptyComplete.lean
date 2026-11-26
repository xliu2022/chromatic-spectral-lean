module

public import ChromaticSpectral.ExtremalColoring

/-! # Nonempty complete colourings and positive extremal values
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r k : ℕ}

theorem exists_complete_edges_nonempty (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hn : r ≤ Fintype.card V) :
    ∃ c : V → Fin k, (RGraph.completeOfColoring r c).edges.Nonempty := by
  classical
  obtain ⟨e, _, hec⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset V)) (by simpa using hn)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < e.card by omega)
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  let c : V → Fin k := fun w => if w = a then z else o
  refine ⟨c, e, (RGraph.mem_completeOfColoring c e).mpr ⟨hec, a, ha, b, hb, ?_⟩⟩
  simp [c, hab.symm, z, o, Fin.ext_iff]

theorem RGraph.pSpectralRadius_eq_zero_of_edges_empty (G : RGraph V r)
    {p : ℝ} (hp : 0 < p) (hG : G.edges = ∅) : G.pSpectralRadius p = 0 := by
  apply le_antisymm _ (G.pSpectralRadius_nonneg hp)
  apply (G.pSpectralRadius_le_iff hp le_rfl).mpr
  intro x _
  simp [polyform, edgePolynomial, hG]

theorem RGraph.edges_nonempty_of_pSpectralRadius_pos (G : RGraph V r)
    {p : ℝ} (hp : 0 < p) (hG : 0 < G.pSpectralRadius p) : G.edges.Nonempty := by
  by_contra h
  rw [G.pSpectralRadius_eq_zero_of_edges_empty hp (Finset.not_nonempty_iff_eq_empty.mp h)] at hG
  exact lt_irrefl 0 hG

theorem IsExtremalColoring.edges_nonempty [Nonempty V] {p : ℝ} {c : V → Fin k}
    (hc : IsExtremalColoring r p c) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hn : r ≤ Fintype.card V) (hp : 0 < p) :
    (RGraph.completeOfColoring r c).edges.Nonempty := by
  obtain ⟨d, hd⟩ := exists_complete_edges_nonempty (V := V) hr hk hn
  apply RGraph.edges_nonempty_of_pSpectralRadius_pos _ hp
  exact ((RGraph.completeOfColoring r d).pSpectralRadius_pos_of_edges_nonempty hp hd).trans_le (hc d)

theorem rank_le_card_of_chromatic_threshold (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hn : (r - 1) * k < Fintype.card V) : r ≤ Fintype.card V := by
  have hm : r - 1 ≤ (r - 1) * k := by simpa using Nat.mul_le_mul_left (r - 1) hk
  omega

end ChromaticSpectral
