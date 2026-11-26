module

public import ChromaticSpectral.CompleteAveraging

/-! # Positivity of all maximizing vectors

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.

A zero coordinate forces its whole colour class to vanish. Averaging it with
a positive coordinate strictly increases the full elementary symmetric sum,
while no monochromatic defect increases. This works uniformly for every p ≥ 1.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

theorem esymmOn_eq_zero_of_support_subset {s t : Finset V} {r : ℕ}
    {x : V → ℝ} (hx : ∀ w ∈ s, w ∉ t → x w = 0) (ht : t.card < r) :
    esymmOn s r x = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨hes, hec⟩ := Finset.mem_powersetCard.mp he
  have hnot : ¬ e ⊆ t := by
    intro h
    have hc := Finset.card_le_card h
    omega
  obtain ⟨w, hwe, hwt⟩ := Finset.not_subset.mp hnot
  exact Finset.prod_eq_zero hwe (hx w (hes hwe) hwt)

theorem esymmOn_pos_of_positive_subset {s e : Finset V} {r : ℕ}
    {x : V → ℝ} (hx : ∀ w ∈ s, 0 ≤ x w) (hes : e ⊆ s)
    (hec : e.card = r) (he : ∀ w ∈ e, 0 < x w) : 0 < esymmOn s r x := by
  have hprod : 0 < ∏ w ∈ e, x w := Finset.prod_pos he
  exact hprod.trans_le (Finset.single_le_sum
    (fun f hf => Finset.prod_nonneg fun w hw => hx w ((Finset.mem_powersetCard.mp hf).1 hw))
    (Finset.mem_powersetCard.mpr ⟨hes, hec⟩))

theorem RGraph.complete_maximizer_pos [Nonempty V]
    {r k : ℕ} (hr : 3 ≤ r) (c : V → Fin k) {p : ℝ} (hp : 1 ≤ p)
    (hQ : (completeOfColoring r c).edges.Nonempty) {x : V → ℝ}
    (hx : (completeOfColoring r c).IsMaximizer p x) : ∀ v, 0 < x v := by
  intro v
  by_contra hnot
  have hv0 : x v = 0 := le_antisymm (not_lt.mp hnot) (hx.1.1 v)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hP : 0 < (completeOfColoring r c).polyform x := by
    rw [hx.2]
    exact pSpectralRadius_pos_of_edges_nonempty _ hp0 hQ
  obtain ⟨e, he, hex⟩ := exists_positive_edge _ hx.1.1 hP
  have hec := (completeOfColoring r c).uniform e he
  have henon : e.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hue⟩ := henon
  have hu0 := hex u hue
  have hne : u ≠ v := by intro h; subst v; linarith
  have hzclass : ∀ w ∈ classSet c (c v), x w = 0 := by
    intro w hw
    have hh := complete_maximizer_constant_on_classes hr c hp hQ hx
      ((mem_classSet c (c v) w).mp hw)
    exact hh.trans hv0
  have hcne : c u ≠ c v := by
    intro hh
    have hh' := hzclass u ((mem_classSet c (c v) u).mpr hh)
    linarith
  have h1 := Finset.pred_card_le_card_erase (s := e) (a := u)
  have h2 := Finset.pred_card_le_card_erase (s := e.erase u) (a := v)
  obtain ⟨f, hf, hfc⟩ := Finset.exists_subset_card_eq
    (show r - 2 ≤ ((e.erase u).erase v).card by omega)
  have hft : f ⊆ ((Finset.univ : Finset V).erase u).erase v := by
    intro w hw
    obtain ⟨hwv, hwrest⟩ := Finset.mem_erase.mp (hf hw)
    have hwu := (Finset.mem_erase.mp hwrest).1
    exact Finset.mem_erase.mpr ⟨hwv,
      Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ w⟩⟩
  have hfpos : ∀ w ∈ f, 0 < x w := by
    intro w hw
    exact hex w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hf hw)))
  have hcoef := esymmOn_pos_of_positive_subset (fun w _ => hx.1.1 w) hft hfc hfpos
  have hdiff := esymmOn_pairAverage_sub (Finset.mem_univ u)
    (Finset.mem_univ v) hne (r - 2) x
  have hr2 : r - 2 + 2 = r := by omega
  rw [hr2] at hdiff
  have hfull : esymmOn Finset.univ r x < esymmOn Finset.univ r (pairAverage x u v) := by
    have hs : 0 < (x u - x v) ^ 2 / 4 := by rw [hv0, sub_zero]; positivity
    have hh := mul_pos hs hcoef
    rw [← hdiff] at hh
    exact sub_pos.mp hh
  have hdefect : ∀ i, esymmOn (classSet c i) r (pairAverage x u v) ≤
      esymmOn (classSet c i) r x := by
    intro i
    by_cases hi : i = c v
    · subst i
      have hnew : esymmOn (classSet c (c v)) r (pairAverage x u v) = 0 := by
        apply esymmOn_eq_zero_of_support_subset (t := {v})
        · intro w hw hwv
          have hwv' : w ≠ v := by simpa using hwv
          have hwu : w ≠ u := by
            intro hh
            subst w
            exact hcne ((mem_classSet c (c v) u).mp hw)
          rw [pairAverage, twoUpdate_apply_of_ne x hwu hwv']
          exact hzclass w hw
        · simp; omega
      rw [hnew]
      exact esymmOn_nonneg (fun w _ => hx.1.1 w) r
    · apply esymmOn_mono (fun w _ => pairAverage_nonneg hx.1.1 u v w)
      intro w hw
      have hwv : w ≠ v := by
        intro hh
        subst w
        exact hi ((mem_classSet c i v).mp hw).symm
      by_cases hwu : w = u
      · subst w
        rw [pairAverage, twoUpdate_apply_left x hne, hv0]
        linarith
      · rw [pairAverage, twoUpdate_apply_of_ne x hwu hwv]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hdefect i)
  have hinc : (completeOfColoring r c).edgePolynomial x <
      (completeOfColoring r c).edgePolynomial (pairAverage x u v) := by
    rw [complete_edgePolynomial c (by omega), complete_edgePolynomial c (by omega)]
    linarith
  have hmass : ∑ w, (pairAverage x u v w) ^ p ≤ 1 :=
    (pairAverage_mass_le hx.1.1 hp hne).trans_eq hx.1.2
  have hupper := (completeOfColoring r c).polyform_le_of_mass_le_one hp0 (by omega)
    (pairAverage_nonneg hx.1.1 u v) hmass
  have hpolyinc := mul_lt_mul_of_pos_left hinc (by positivity : (0 : ℝ) < r.factorial)
  change (completeOfColoring r c).polyform x < _ at hpolyinc
  rw [hx.2] at hpolyinc
  exact (not_lt_of_ge hupper) hpolyinc

theorem RGraph.pSpectralRadius_strictMono_complete [Nonempty V]
    {r k : ℕ} (hr : 3 ≤ r) (c : V → Fin k) {p : ℝ} (hp : 1 ≤ p)
    {G : RGraph V r} (hG : G.edges ⊂ (completeOfColoring r c).edges) :
    G.pSpectralRadius p < (completeOfColoring r c).pSpectralRadius p := by
  have hQ : (completeOfColoring r c).edges.Nonempty := by
    obtain ⟨e, he, _⟩ := Finset.exists_of_ssubset hG
    exact ⟨e, he⟩
  exact pSpectralRadius_strictMono_of_all_maximizers_pos (by linarith) hG
    (fun x hx => complete_maximizer_pos hr c hp hQ hx)

end ChromaticSpectral
