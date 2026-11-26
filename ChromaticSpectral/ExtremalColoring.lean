module

public import ChromaticSpectral.Positivity
public import ChromaticSpectral.ClassMove

/-! # Extremal colourings and the one-vertex comparison
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r k : ℕ}

def IsExtremalColoring (r : ℕ) (p : ℝ) (c : V → Fin k) : Prop :=
  ∀ d : V → Fin k,
    (RGraph.completeOfColoring r d).pSpectralRadius p ≤
      (RGraph.completeOfColoring r c).pSpectralRadius p

theorem exists_extremalColoring (r : ℕ) (p : ℝ) (c₀ : V → Fin k) :
    ∃ c : V → Fin k, IsExtremalColoring r p c := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ
    (fun c : V → Fin k => (RGraph.completeOfColoring r c).pSpectralRadius p)
    ⟨c₀, Finset.mem_univ c₀⟩
  exact ⟨c, fun d => hc d (Finset.mem_univ d)⟩

theorem IsExtremalColoring.link_le {p : ℝ} {c : V → Fin k}
    (hc : IsExtremalColoring r p c) (hr : 0 < r) (hp : 0 < p)
    {x : V → ℝ} (hx : (RGraph.completeOfColoring r c).IsMaximizer p x)
    {v : V} (hxv : 0 < x v) {j : Fin k} (hj : j ≠ c v) :
    esymmOn ((classSet c (c v)).erase v) (r - 1) x ≤
      esymmOn (classSet c j) (r - 1) x := by
  have hP := ((RGraph.completeOfColoring r (Function.update c v j)).polyform_le_pSpectralRadius
    hp hx.1).trans (hc (Function.update c v j))
  rw [← hx.2] at hP
  have hf : (0 : ℝ) < r.factorial := by positivity
  have hE : (RGraph.completeOfColoring r (Function.update c v j)).edgePolynomial x ≤
      (RGraph.completeOfColoring r c).edgePolynomial x := by
    unfold RGraph.polyform at hP
    nlinarith
  have hmove := RGraph.complete_classMove c v hj (r - 1) x
  rw [Nat.sub_add_cancel hr] at hmove
  have hprod : x v * (esymmOn ((classSet c (c v)).erase v) (r - 1) x -
      esymmOn (classSet c j) (r - 1) x) ≤ 0 := by linarith
  nlinarith

theorem exists_large_class (c : V → Fin k) (s : ℕ)
    (hn : s * k < Fintype.card V) : ∃ i, s < classSize c i := by
  by_contra hh
  push Not at hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hh i)
  rw [classSize_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact (not_le_of_gt hn) (by simpa only [Nat.mul_comm] using hsum)

theorem IsExtremalColoring.classSize_lower [Nonempty V]
    {p : ℝ} {c : V → Fin k} (hc : IsExtremalColoring r p c)
    (hr : 3 ≤ r) (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V)
    (hQ : (RGraph.completeOfColoring r c).edges.Nonempty) :
    ∀ j, r - 1 ≤ classSize c j := by
  obtain ⟨x, hx1, hx2⟩ := (RGraph.completeOfColoring r c).exists_maximizer (by linarith)
  have hx : (RGraph.completeOfColoring r c).IsMaximizer p x := ⟨hx1, hx2⟩
  have hxpos := RGraph.complete_maximizer_pos hr c hp hQ hx
  obtain ⟨i, hi⟩ := exists_large_class c (r - 1) hn
  have hinon : (classSet c i).Nonempty := Finset.card_pos.mp (by rw [classSet_card]; omega)
  obtain ⟨v, hv⟩ := hinon
  have hvi := (mem_classSet c i v).mp hv
  intro j
  by_contra hjbound
  have hjlt : classSize c j < r - 1 := lt_of_not_ge hjbound
  have hj : j ≠ c v := by
    intro h
    rw [h, hvi] at hjlt
    omega
  have hlink := hc.link_le (by omega) (by linarith) hx (hxpos v) hj
  have hz : esymmOn (classSet c j) (r - 1) x = 0 :=
    esymmOn_eq_zero_of_card_lt (by simpa using hjlt) x
  have hcard : r - 1 ≤ ((classSet c (c v)).erase v).card := by
    rw [Finset.card_erase_of_mem (by simp), classSet_card, hvi]
    omega
  obtain ⟨f, hf, hfc⟩ := Finset.exists_subset_card_eq hcard
  have hpos := esymmOn_pos_of_positive_subset (fun w _ => (hxpos w).le) hf hfc
    (fun w _ => hxpos w)
  rw [hz] at hlink
  exact (not_lt_of_ge hlink) hpos

theorem IsExtremalColoring.binomial_weight_le [Nonempty V]
    {p : ℝ} {c : V → Fin k} (hc : IsExtremalColoring r p c)
    (hr : 3 ≤ r) (hp : 1 ≤ p)
    (hQ : (RGraph.completeOfColoring r c).edges.Nonempty)
    {x : V → ℝ} (hx : (RGraph.completeOfColoring r c).IsMaximizer p x)
    {u v : V} (huv : c u ≠ c v) :
    ((classSize c (c u) - 1).choose (r - 1) : ℝ) * (x u) ^ (r - 1) ≤
      ((classSize c (c v)).choose (r - 1) : ℝ) * (x v) ^ (r - 1) := by
  have hxpos := RGraph.complete_maximizer_pos hr c hp hQ hx
  have hl := hc.link_le (by omega) (by linarith) hx (hxpos u) huv.symm
  have hold : esymmOn ((classSet c (c u)).erase u) (r - 1) x =
      ((classSize c (c u) - 1).choose (r - 1) : ℝ) * (x u) ^ (r - 1) := by
    calc
      _ = esymmOn ((classSet c (c u)).erase u) (r - 1) (fun _ => x u) := by
        apply esymmOn_congr
        intro w hw
        exact RGraph.complete_maximizer_constant_on_classes hr c hp hQ hx
          ((mem_classSet c (c u) w).mp (Finset.mem_of_mem_erase hw))
      _ = _ := by
        rw [esymmOn_const, Finset.card_erase_of_mem (by simp), classSet_card]
  have hnew : esymmOn (classSet c (c v)) (r - 1) x =
      ((classSize c (c v)).choose (r - 1) : ℝ) * (x v) ^ (r - 1) := by
    calc
      _ = esymmOn (classSet c (c v)) (r - 1) (fun _ => x v) := by
        apply esymmOn_congr
        intro w hw
        exact RGraph.complete_maximizer_constant_on_classes hr c hp hQ hx
          ((mem_classSet c (c v) w).mp hw)
      _ = _ := by rw [esymmOn_const, classSet_card]
  simpa only [hold, hnew] using hl

end ChromaticSpectral
