module

public import ChromaticSpectral.Basic

/-! # Weak colourings and their complete hypergraphs
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r k : ℕ}

@[simp] theorem RGraph.mem_completeOfColoring (c : V → Fin k) (e : Finset V) :
    e ∈ (RGraph.completeOfColoring r c).edges ↔
      e.card = r ∧ ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v := by
  classical
  simp [RGraph.completeOfColoring, Finset.mem_powersetCard]

theorem RGraph.completeOfColoring_proper (c : V → Fin k) :
    (RGraph.completeOfColoring r c).IsProperColoring c := by
  intro e he
  exact (mem_completeOfColoring c e).mp he |>.2

theorem RGraph.completeOfColoring_colorable (c : V → Fin k) :
    (RGraph.completeOfColoring r c).Colorable k :=
  ⟨c, completeOfColoring_proper c⟩

theorem RGraph.subgraph_complete_iff (G : RGraph V r) (c : V → Fin k) :
    G.IsSubgraph (RGraph.completeOfColoring r c) ↔ G.IsProperColoring c := by
  constructor
  · intro h e he
    exact (mem_completeOfColoring c e).mp (h he) |>.2
  · intro h e he
    exact (mem_completeOfColoring c e).mpr ⟨G.uniform e he, h e he⟩

theorem classSize_sum (c : V → Fin k) :
    ∑ i, classSize c i = Fintype.card V := by
  classical
  unfold classSize
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem classSize_le_card (c : V → Fin k) (i : Fin k) :
    classSize c i ≤ Fintype.card V :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem classSize_eq_zero_iff (c : V → Fin k) (i : Fin k) :
    classSize c i = 0 ↔ ∀ v, c v ≠ i := by
  classical
  simp [classSize, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem RGraph.colorable_mono {G H : RGraph V r} (h : G.IsSubgraph H)
    (hH : H.Colorable k) : G.Colorable k := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c, fun e he => hc e (h he)⟩

theorem RGraph.isBalancedComplete_colorable {G : RGraph V r}
    (h : G.IsBalancedComplete k) : G.Colorable k := by
  obtain ⟨c, _, rfl⟩ := h
  exact completeOfColoring_colorable c

/-- A monochromatic nonempty finite set has a unique colour. -/
theorem not_nonmono_iff {c : V → Fin k} {e : Finset V} (he : e.Nonempty) :
    ¬ (∃ u ∈ e, ∃ v ∈ e, c u ≠ c v) ↔ ∃ i, ∀ v ∈ e, c v = i := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := he
    refine ⟨c u, ?_⟩
    intro v hv
    by_contra hne
    exact h ⟨v, hv, u, hu, hne⟩
  · rintro ⟨i, hi⟩ ⟨u, hu, v, hv, hne⟩
    exact hne ((hi u hu).trans (hi v hv).symm)

end ChromaticSpectral
