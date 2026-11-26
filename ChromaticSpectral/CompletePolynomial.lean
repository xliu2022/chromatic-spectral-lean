module

public import ChromaticSpectral.Coloring
public import ChromaticSpectral.SpectralBasic

/-! # The complete-colouring polynomial and its monochromatic defects
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r k : ℕ}

noncomputable def classSet (c : V → Fin k) (i : Fin k) : Finset V :=
  Finset.univ.filter (fun v => c v = i)

@[simp] theorem mem_classSet (c : V → Fin k) (i : Fin k) (v : V) :
    v ∈ classSet c i ↔ c v = i := by
  classical
  simp [classSet]

@[simp] theorem classSet_card (c : V → Fin k) (i : Fin k) :
    (classSet c i).card = classSize c i := rfl

theorem powersetCard_classSet (c : V → Fin k) (i : Fin k) (r : ℕ) :
    (classSet c i).powersetCard r =
      (Finset.univ.powersetCard r).filter (fun e => ∀ v ∈ e, c v = i) := by
  classical
  ext e
  simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hsub, hcard⟩
    exact ⟨hcard, fun v hv => (mem_classSet c i v).mp (hsub hv)⟩
  · rintro ⟨hcard, hmono⟩
    exact ⟨fun v hv => (mem_classSet c i v).mpr (hmono v hv), hcard⟩

theorem esymmOn_classSet_eq_sum (c : V → Fin k) (i : Fin k) (r : ℕ) (x : V → ℝ) :
    esymmOn (classSet c i) r x =
      ∑ e ∈ Finset.univ.powersetCard r,
        if (∀ v ∈ e, c v = i) then ∏ v ∈ e, x v else 0 := by
  classical
  rw [esymmOn, powersetCard_classSet, Finset.sum_filter]

theorem sum_mono_indicator (c : V → Fin k) {e : Finset V} (he : e.Nonempty)
    (w : ℝ) :
    (∑ i : Fin k, if (∀ v ∈ e, c v = i) then w else 0) =
      if (∃ u ∈ e, ∃ v ∈ e, c u ≠ c v) then 0 else w := by
  classical
  by_cases h : ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v
  · rw [if_pos h]
    apply Finset.sum_eq_zero
    intro i _
    apply if_neg
    rintro hi
    obtain ⟨u, hu, v, hv, hne⟩ := h
    exact hne ((hi u hu).trans (hi v hv).symm)
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := (not_nonmono_iff he).mp h
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j _ hji
      apply if_neg
      intro hj
      obtain ⟨v, hv⟩ := he
      exact hji ((hj v hv).symm.trans (hi v hv))
    · simp

theorem RGraph.complete_edgePolynomial_add_defects (c : V → Fin k)
    (hr : 0 < r) (x : V → ℝ) :
    (RGraph.completeOfColoring r c).edgePolynomial x +
      ∑ i, esymmOn (classSet c i) r x = esymmOn Finset.univ r x := by
  classical
  simp_rw [esymmOn_classSet_eq_sum]
  rw [Finset.sum_comm]
  have hh : (∑ e ∈ Finset.univ.powersetCard r,
      ∑ i : Fin k, if (∀ v ∈ e, c v = i) then ∏ v ∈ e, x v else 0) =
      ∑ e ∈ Finset.univ.powersetCard r,
        if (∃ u ∈ e, ∃ v ∈ e, c u ≠ c v) then 0 else ∏ v ∈ e, x v := by
    apply Finset.sum_congr rfl
    intro e he
    apply sum_mono_indicator
    apply Finset.card_pos.mp
    simpa [(Finset.mem_powersetCard.mp he).2] using hr
  rw [hh]
  simp only [RGraph.edgePolynomial, RGraph.completeOfColoring, Finset.sum_filter, esymmOn]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

theorem RGraph.complete_edgePolynomial (c : V → Fin k)
    (hr : 0 < r) (x : V → ℝ) :
    (RGraph.completeOfColoring r c).edgePolynomial x =
      esymmOn Finset.univ r x - ∑ i, esymmOn (classSet c i) r x := by
  have h := complete_edgePolynomial_add_defects c hr x
  linarith

theorem RGraph.complete_edge_count (c : V → Fin k) (hr : 0 < r) :
    ((RGraph.completeOfColoring r c).edges.card : ℝ) =
      ((Fintype.card V).choose r : ℝ) - ∑ i, ((classSize c i).choose r : ℝ) := by
  have h := complete_edgePolynomial c hr (fun _ => (1 : ℝ))
  simpa [edgePolynomial_const, esymmOn, Finset.prod_const] using h

end ChromaticSpectral
