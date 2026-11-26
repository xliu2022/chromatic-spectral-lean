module

public import ChromaticSpectral.ClassStationarity

/-! # Order and equality of the class weights at a Lagrangian maximum
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] [Nonempty V] {r k : ℕ}

theorem esymmOn_erase_pair_pos {x : V → ℝ} (hx : ∀ w, 0 < x w)
    {u v : V} (hne : u ≠ v) (hr : 2 ≤ r) (hn : r ≤ Fintype.card V) :
    0 < esymmOn ((Finset.univ.erase u).erase v) (r - 2) x := by
  have hc : r - 2 ≤ (((Finset.univ : Finset V).erase u).erase v).card := by
    rw [Finset.card_erase_of_mem (by simp [hne.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
    omega
  obtain ⟨f, hf, hfc⟩ := Finset.exists_subset_card_eq hc
  exact esymmOn_pos_of_positive_subset (fun w _ => (hx w).le) hf hfc (fun w _ => hx w)

theorem RGraph.complete_maximizer_classLink (hr : 3 ≤ r) (c : V → Fin k)
    {p : ℝ} (hp : 1 ≤ p) (hQ : (completeOfColoring r c).edges.Nonempty)
    {x : V → ℝ} (hx : (completeOfColoring r c).IsMaximizer p x) (u : V) :
    esymmOn ((classSet c (c u)).erase u) (r - 1) x =
      ((classSize c (c u) - 1).choose (r - 1) : ℝ) * (x u) ^ (r - 1) := by
  calc
    _ = esymmOn ((classSet c (c u)).erase u) (r - 1) (fun _ => x u) := by
      apply esymmOn_congr
      intro w hw
      exact complete_maximizer_constant_on_classes hr c hp hQ hx
        ((mem_classSet c (c u) w).mp (Finset.mem_of_mem_erase hw))
    _ = _ := by
      rw [esymmOn_const, Finset.card_erase_of_mem (by simp), classSet_card]

theorem RGraph.complete_maximizer_binomial_stationarity (hr : 3 ≤ r) (c : V → Fin k)
    (hQ : (completeOfColoring r c).edges.Nonempty) {x : V → ℝ}
    (hx : (completeOfColoring r c).IsMaximizer 1 x) {u v : V} (hc : c u ≠ c v) :
    (x v - x u) * esymmOn ((Finset.univ.erase u).erase v) (r - 2) x =
      ((classSize c (c u) - 1).choose (r - 1) : ℝ) * (x u) ^ (r - 1) -
      ((classSize c (c v) - 1).choose (r - 1) : ℝ) * (x v) ^ (r - 1) := by
  have hh := complete_maximizer_link_difference hr c hQ hx hc
  rw [complete_maximizer_classLink hr c (by norm_num) hQ hx u,
    complete_maximizer_classLink hr c (by norm_num) hQ hx v] at hh
  linarith

theorem RGraph.complete_maximizer_weight_antitone (hr : 3 ≤ r) (c : V → Fin k)
    (hQ : (completeOfColoring r c).edges.Nonempty) {x : V → ℝ}
    (hx : (completeOfColoring r c).IsMaximizer 1 x) {u v : V}
    (hsize : classSize c (c v) ≤ classSize c (c u)) : x u ≤ x v := by
  by_contra hnot
  have hlt : x v < x u := lt_of_not_ge hnot
  by_cases hc : c u = c v
  · have hh := complete_maximizer_constant_on_classes hr c (by norm_num) hQ hx hc
    linarith
  have hne : u ≠ v := fun h => hc (congrArg c h)
  have hxpos := complete_maximizer_pos hr c (by norm_num) hQ hx
  have hn : r ≤ Fintype.card V := by
    obtain ⟨e, he⟩ := hQ
    have hh := Finset.card_le_univ e
    rwa [(completeOfColoring r c).uniform e he] at hh
  have hE := esymmOn_erase_pair_pos hxpos hne (by omega) hn
  have hcoeff : ((classSize c (c v) - 1).choose (r - 1) : ℝ) ≤
      ((classSize c (c u) - 1).choose (r - 1) : ℝ) := by
    exact_mod_cast Nat.choose_le_choose (r - 1) (Nat.sub_le_sub_right hsize 1)
  have hpow : (x v) ^ (r - 1) ≤ (x u) ^ (r - 1) :=
    pow_le_pow_left₀ (hxpos v).le hlt.le _
  have hprod := mul_le_mul hcoeff hpow (pow_nonneg (hxpos v).le _)
    (show (0 : ℝ) ≤ (classSize c (c u) - 1).choose (r - 1) by positivity)
  have hh := complete_maximizer_binomial_stationarity hr c hQ hx hc
  have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hE
  linarith

theorem RGraph.complete_maximizer_equal_of_classSize_eq (hr : 3 ≤ r) (c : V → Fin k)
    (hQ : (completeOfColoring r c).edges.Nonempty) {x : V → ℝ}
    (hx : (completeOfColoring r c).IsMaximizer 1 x) {u v : V}
    (hsize : classSize c (c u) = classSize c (c v)) : x u = x v := by
  exact le_antisymm (complete_maximizer_weight_antitone hr c hQ hx hsize.ge)
    (complete_maximizer_weight_antitone hr c hQ hx hsize.le)

end ChromaticSpectral
