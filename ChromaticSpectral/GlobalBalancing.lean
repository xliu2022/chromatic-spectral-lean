module

public import ChromaticSpectral.EsymmConvolution
public import ChromaticSpectral.ClassMove

/-! # Passing from local smoothing to the complete hypergraph
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {k r : ℕ}

theorem disjoint_classSet (c : V → Fin k) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (classSet c i) (classSet c j) := by
  apply Finset.disjoint_left.mpr
  intro w hwi hwj
  exact hij (((mem_classSet c i w).mp hwi).symm.trans ((mem_classSet c j w).mp hwj))

/-- A local replacement improves the whole graph if all full layers improve,
all layers in the shrinking class decrease, and the pure crossing layer improves
strictly. Weights outside the local set only need to be nonnegative; they need
not be constant within their colour classes. -/
theorem RGraph.complete_local_improvement (hr : 0 < r) (c : V → Fin k)
    {v : V} {j : Fin k} (hj : j ≠ c v) {C : Finset V}
    (hC : C ⊆ classSet c (c v)) (hv : v ∈ C) {x y : V → ℝ}
    (hx : ∀ w, 0 ≤ x w)
    (hout : ∀ w, w ∉ C ∪ classSet c j → y w = x w)
    (hfull : ∀ s, esymmOn (C ∪ classSet c j) s x ≤ esymmOn (C ∪ classSet c j) s y)
    (hclass : ∀ s, esymmOn (C.erase v) s y ≤ esymmOn C s x)
    (hpure : esymmOn (C ∪ classSet c j) r x - esymmOn C r x -
        esymmOn (classSet c j) r x <
      esymmOn (C ∪ classSet c j) r y - esymmOn (C.erase v) r y -
        esymmOn (insert v (classSet c j)) r y) :
    (completeOfColoring r c).edgePolynomial x <
      (completeOfColoring r (Function.update c v j)).edgePolynomial y := by
  let S := C ∪ classSet c j
  let E := classSet c (c v) \ C
  let R := (Finset.univ : Finset V) \ S
  have hCE : Disjoint C E := Finset.disjoint_sdiff
  have hCE' : Disjoint (C.erase v) E := hCE.mono_left (Finset.erase_subset v C)
  have hSR : Disjoint S R := Finset.disjoint_sdiff
  have hsource : C ∪ E = classSet c (c v) := Finset.union_sdiff_of_subset hC
  have hsource' : C.erase v ∪ E = (classSet c (c v)).erase v := by
    have hvE : v ∉ E := by simp [E, hv]
    rw [← hsource, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hvE]
  have hwhole : S ∪ R = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ S)
  have hEout : ∀ w ∈ E, w ∉ S := by
    intro w hw hws
    obtain ⟨hwclass, hwC⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp hws with hwS | hwB
    · exact hwC hwS
    · exact (Finset.disjoint_left.mp (disjoint_classSet c hj.symm)) hwclass hwB
  have hEy : ∀ w ∈ E, y w = x w := fun w hw => hout w (hEout w hw)
  have hRy : ∀ w ∈ R, y w = x w := fun w hw => hout w (Finset.mem_sdiff.mp hw).2
  have htotal := esymmOn_union_difference hSR hSR r hRy
  rw [hwhole] at htotal
  have hsrc := esymmOn_union_difference hCE hCE' r hEy
  rw [hsource, hsource'] at hsrc
  have hsum := sum_sub_eq_pair
    (fun i => esymmOn (classSet (Function.update c v j) i) r y)
    (fun i => esymmOn (classSet c i) r x) hj.symm
    (by
      intro i hi hij
      rw [classSet_update_other c v hi hij]
      apply esymmOn_congr
      intro w hw
      apply hout
      intro hws
      have hwi := (mem_classSet c i w).mp hw
      rcases Finset.mem_union.mp hws with hwC | hwB
      · have hwold := (mem_classSet c (c v) w).mp (hC hwC)
        exact hi (hwi.symm.trans hwold)
      · have hwj := (mem_classSet c j w).mp hwB
        exact hij (hwi.symm.trans hwj))
  rw [classSet_update_old c v hj, classSet_update_new c v hj] at hsum
  have htotal_nonneg : 0 ≤ ∑ i ∈ Finset.range r,
      (esymmOn S i y - esymmOn S i x) * esymmOn R (r - i) x := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (hfull i)) (esymmOn_nonneg (fun w _ => hx w) _)
  have hsrc_nonpos : (∑ i ∈ Finset.range r,
      (esymmOn (C.erase v) i y - esymmOn C i x) * esymmOn E (r - i) x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hclass i))
      (esymmOn_nonneg (fun w _ => hx w) _)
  rw [complete_edgePolynomial _ hr, complete_edgePolynomial _ hr]
  change esymmOn S r x - esymmOn C r x - esymmOn (classSet c j) r x <
      esymmOn S r y - esymmOn (C.erase v) r y - esymmOn (insert v (classSet c j)) r y at hpure
  linarith

end ChromaticSpectral
