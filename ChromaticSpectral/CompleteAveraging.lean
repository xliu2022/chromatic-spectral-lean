module

public import ChromaticSpectral.Averaging

/-! # Strict averaging inside a colour class
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {k : ℕ}

theorem esymmOn_pairAverage_class_of_ne (c : V → Fin k) (x : V → ℝ)
    {u v : V} (hc : c u = c v) {i : Fin k} (hi : i ≠ c u) (r : ℕ) :
    esymmOn (classSet c i) r (pairAverage x u v) = esymmOn (classSet c i) r x := by
  apply esymmOn_congr
  intro w hw
  have hwi := (mem_classSet c i w).mp hw
  have hwu : w ≠ u := by intro h; subst w; exact hi hwi.symm
  have hwv : w ≠ v := by intro h; subst w; exact hi (hwi.symm.trans hc.symm)
  exact twoUpdate_apply_of_ne x hwu hwv _ _

theorem RGraph.complete_pairAverage_sub (c : V → Fin k) (x : V → ℝ)
    {u v : V} (hne : u ≠ v) (hc : c u = c v) (j : ℕ) :
    (completeOfColoring (j + 2) c).edgePolynomial (pairAverage x u v) -
      (completeOfColoring (j + 2) c).edgePolynomial x =
      (x u - x v) ^ 2 / 4 *
        (esymmOn ((Finset.univ.erase u).erase v) j x -
          esymmOn (((classSet c (c u)).erase u).erase v) j x) := by
  have hu : u ∈ classSet c (c u) := by simp
  have hv : v ∈ classSet c (c u) := by simpa using hc.symm
  have hall := esymmOn_pairAverage_sub (Finset.mem_univ u) (Finset.mem_univ v) hne j x
  have hclass := esymmOn_pairAverage_sub hu hv hne j x
  have hsum : (∑ i, esymmOn (classSet c i) (j + 2) (pairAverage x u v)) -
      (∑ i, esymmOn (classSet c i) (j + 2) x) =
      esymmOn (classSet c (c u)) (j + 2) (pairAverage x u v) -
        esymmOn (classSet c (c u)) (j + 2) x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single (c u)
    · intro i _ hi
      rw [esymmOn_pairAverage_class_of_ne c x hc hi, sub_self]
    · simp
  rw [complete_edgePolynomial c (by omega), complete_edgePolynomial c (by omega)]
  linear_combination hall - hsum - hclass

theorem RGraph.exists_positive_edge {r : ℕ} (G : RGraph V r) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hP : 0 < G.polyform x) :
    ∃ e ∈ G.edges, ∀ v ∈ e, 0 < x v := by
  have hS : 0 < G.edgePolynomial x := by
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < r.factorial)).mp hP
  obtain ⟨e, he, hprod⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun e (_ : e ∈ G.edges) => Finset.prod_nonneg (fun v _ => hx v))).mp hS
  refine ⟨e, he, ?_⟩
  intro v hv
  apply lt_of_le_of_ne (hx v)
  intro hz
  have hzero : ∏ w ∈ e, x w = 0 := Finset.prod_eq_zero hv hz.symm
  linarith

/-- Extract a positive subedge of a prescribed size containing a distinguished
vertex, while avoiding two other vertices. -/
theorem exists_subset_erase_pair_containing {e : Finset V} {u v z : V}
    {j : ℕ} (hz : z ∈ e) (hzu : z ≠ u) (hzv : z ≠ v)
    (hj : 0 < j) (hcard : j + 2 ≤ e.card) :
    ∃ f : Finset V, f ⊆ e ∧ u ∉ f ∧ v ∉ f ∧ z ∈ f ∧ f.card = j := by
  have h1 := Finset.pred_card_le_card_erase (s := e) (a := u)
  have h2 := Finset.pred_card_le_card_erase (s := e.erase u) (a := v)
  have h3 := Finset.pred_card_le_card_erase (s := (e.erase u).erase v) (a := z)
  have hsmall : j - 1 ≤ (((e.erase u).erase v).erase z).card := by omega
  obtain ⟨f, hf, hfc⟩ := Finset.exists_subset_card_eq hsmall
  have hznot : z ∉ f := fun h => Finset.notMem_erase z _ (hf h)
  refine ⟨insert z f, ?_, ?_, ?_, Finset.mem_insert_self _ _, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hz
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hf hw)))
  · simp only [Finset.mem_insert, not_or]
    refine ⟨hzu.symm, ?_⟩
    intro hu
    exact Finset.notMem_erase u e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hf hu)))
  · simp only [Finset.mem_insert, not_or]
    refine ⟨hzv.symm, ?_⟩
    intro hv
    exact Finset.notMem_erase v _ (Finset.mem_of_mem_erase (hf hv))
  · rw [Finset.card_insert_of_notMem hznot, hfc]
    omega

theorem RGraph.complete_maximizer_constant_on_classes [Nonempty V]
    {r : ℕ} (hr : 3 ≤ r) (c : V → Fin k) {p : ℝ} (hp : 1 ≤ p)
    (hQ : (completeOfColoring r c).edges.Nonempty) {x : V → ℝ}
    (hx : (completeOfColoring r c).IsMaximizer p x)
    {u v : V} (hc : c u = c v) : x u = x v := by
  by_contra hweights
  have hne : u ≠ v := by intro h; subst v; exact hweights rfl
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hP : 0 < (completeOfColoring r c).polyform x := by
    rw [hx.2]
    exact pSpectralRadius_pos_of_edges_nonempty _ hp0 hQ
  obtain ⟨e, he, hex⟩ := exists_positive_edge _ hx.1.1 hP
  obtain ⟨hec, a, ha, b, hb, hab⟩ := (mem_completeOfColoring c e).mp he
  have hz : ∃ z ∈ e, c z ≠ c u := by
    by_cases h : c a = c u
    · exact ⟨b, hb, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨a, ha, h⟩
  obtain ⟨z, hze, hzcol⟩ := hz
  have hzu : z ≠ u := fun h => hzcol (congrArg c h)
  have hzv : z ≠ v := fun h => hzcol ((congrArg c h).trans hc.symm)
  obtain ⟨f, hfe, hfu, hfv, hfz, hfc⟩ :=
    exists_subset_erase_pair_containing hze hzu hzv
      (show 0 < r - 2 by omega) (show r - 2 + 2 ≤ e.card by omega)
  have hsub : ((classSet c (c u)).erase u).erase v ⊆
      ((Finset.univ : Finset V).erase u).erase v := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩
  have hft : f ⊆ ((Finset.univ : Finset V).erase u).erase v := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hfv (h ▸ hw), fun h => hfu (h ▸ hw)⟩
  have hfs : ¬ f ⊆ ((classSet c (c u)).erase u).erase v := by
    intro h
    have hzmem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (h hfz))
    exact hzcol ((mem_classSet c (c u) z).mp hzmem)
  have hstrict := esymmOn_strictMono_set hsub (fun w _ => hx.1.1 w) hft hfc hfs
    (Finset.prod_pos fun w hw => hex w (hfe hw))
  have hdiff := complete_pairAverage_sub c x hne hc (r - 2)
  have hr2 : r - 2 + 2 = r := by omega
  rw [hr2] at hdiff
  have hinc : (completeOfColoring r c).edgePolynomial x <
      (completeOfColoring r c).edgePolynomial (pairAverage x u v) := by
    have hcoef : 0 < (x u - x v) ^ 2 / 4 :=
      div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hweights)) (by norm_num)
    have hh := mul_pos hcoef (sub_pos.mpr hstrict)
    rw [← hdiff] at hh
    exact sub_pos.mp hh
  have hmass : ∑ w, (pairAverage x u v w) ^ p ≤ 1 := by
    exact (pairAverage_mass_le hx.1.1 hp hne).trans_eq hx.1.2
  have hupper := (completeOfColoring r c).polyform_le_of_mass_le_one hp0 (by omega)
    (pairAverage_nonneg hx.1.1 u v) hmass
  have hpolyinc := mul_lt_mul_of_pos_left hinc (by positivity : (0 : ℝ) < r.factorial)
  change (completeOfColoring r c).polyform x < _ at hpolyinc
  rw [hx.2] at hpolyinc
  exact (not_lt_of_ge hupper) hpolyinc

end ChromaticSpectral
