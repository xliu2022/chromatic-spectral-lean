module

public import ChromaticSpectral.NonemptyComplete
public import ChromaticSpectral.WeightedBinomial
public import ChromaticSpectral.LocalVectorSmoothing
public import ChromaticSpectral.GlobalBalancing

/-! # Every extremal colouring is balanced
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] [Nonempty V] {r k : ℕ}

theorem IsExtremalColoring.balanced {p : ℝ} {c : V → Fin k}
    (hc : IsExtremalColoring r p c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V) : BalancedColoring c := by
  have hp0 : 0 < p := by linarith
  have hr3 : 3 ≤ r := by omega
  have hnrank := rank_le_card_of_chromatic_threshold (by omega : 1 ≤ r) (by omega : 1 ≤ k) hn
  have hQ := hc.edges_nonempty (by omega) hk hnrank hp0
  obtain ⟨x, hx1, hx2⟩ := (RGraph.completeOfColoring r c).exists_maximizer hp0
  have hx : (RGraph.completeOfColoring r c).IsMaximizer p x := ⟨hx1, hx2⟩
  have hxpos := RGraph.complete_maximizer_pos hr3 c hp hQ hx
  have hmin := hc.classSize_lower hr3 hp hn hQ
  by_contra hnot
  change ¬ ∀ i j, classSize c i ≤ classSize c j + 1 at hnot
  push Not at hnot
  obtain ⟨i, j, hijsize⟩ := hnot
  have hij : i ≠ j := by intro h; subst j; omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (classSet c i).card by
    rw [classSet_card]; have := hmin i; omega)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (classSet c j).card by
    rw [classSet_card]; have := hmin j; omega)
  have hui := (mem_classSet c i u).mp hu
  have hwj := (mem_classSet c j w).mp hw
  obtain ⟨C, hC, hCcard⟩ := Finset.exists_subset_card_eq
    (s := classSet c i) (n := classSize c j + 2) (by rw [classSet_card]; omega)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
  have hvi := (mem_classSet c i v).mp (hC hv)
  have hjv : j ≠ c v := by rw [hvi]; exact hij.symm
  have hC' : C ⊆ classSet c (c v) := by simpa only [hvi] using hC
  have hCB : Disjoint C (classSet c j) := (disjoint_classSet c hij).mono_left hC
  have hxC : ∀ z ∈ C, x z = x u := by
    intro z hz
    apply RGraph.complete_maximizer_constant_on_classes hr3 c hp hQ hx
    exact ((mem_classSet c i z).mp (hC hz)).trans hui.symm
  have hxB : ∀ z ∈ classSet c j, x z = x w := by
    intro z hz
    apply RGraph.complete_maximizer_constant_on_classes hr3 c hp hQ hx
    exact ((mem_classSet c j z).mp hz).trans hwj.symm
  have hmass₀ := hc.local_mass_ratio hr3 hp hn hQ hx
    (u := u) (v := w) (by rw [hui, hwj]; omega)
  rw [hui, hwj] at hmass₀
  have hfac : ((classSize c j + 1 : ℕ) : ℝ) ≤ ((classSize c i - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show classSize c j + 1 ≤ classSize c i - 1 by omega)
  have hmass : ((classSize c j + 1 : ℕ) : ℝ) * (x u) ^ p ≤
      (((classSize c j + 1 : ℕ) : ℝ) - 1) * (x w) ^ p := by
    have hh := (mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg (hxpos u).le p)).trans hmass₀
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hh
  obtain ⟨W⟩ := exists_localSmoothingWitness (c := classSize c j + 1) (r := r)
    hCB hv (by omega : C.card = classSize c j + 1 + 1)
    (by simp : (classSet c j).card = (classSize c j + 1) - 1)
    hr3 (by have := hmin j; omega) hp hx1.1 (hxpos u) (hxpos w) hxC hxB hmass
  have hinc := RGraph.complete_local_improvement (by omega : 0 < r) c hjv hC' hv hx1.1
    W.outside_eq W.full_le W.class_le W.pure_lt
  have hy : PWeights p W.y := ⟨W.nonneg, W.psum_eq.trans hx1.2⟩
  have hbound := ((RGraph.completeOfColoring r (Function.update c v j)).polyform_le_pSpectralRadius
    hp0 hy).trans (hc (Function.update c v j))
  have hpolyinc := mul_lt_mul_of_pos_left hinc (by positivity : (0 : ℝ) < r.factorial)
  change (RGraph.completeOfColoring r c).polyform x <
    (RGraph.completeOfColoring r (Function.update c v j)).polyform W.y at hpolyinc
  rw [hx2] at hpolyinc
  exact (not_lt_of_ge hbound) hpolyinc

theorem exists_extremal_balanced_coloring (hr : 4 ≤ r) (hk : 2 ≤ k)
    {p : ℝ} (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V) :
    ∃ c : V → Fin k, IsExtremalColoring r p c ∧ BalancedColoring c := by
  let c₀ : V → Fin k := fun _ => ⟨0, by omega⟩
  obtain ⟨c, hc⟩ := exists_extremalColoring r p c₀
  exact ⟨c, hc, hc.balanced hr hk hp hn⟩

end ChromaticSpectral
