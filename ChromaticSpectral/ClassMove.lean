module

public import ChromaticSpectral.CompletePolynomial
public import ChromaticSpectral.ElementarySymmetric

/-! # Moving one labelled vertex between colour classes
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral

theorem sum_sub_eq_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) {a b : ι} (hab : a ≠ b)
    (hfg : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    (∑ i, f i) - ∑ i, g i = (f a - g a) + (f b - g b) := by
  have hrest : (∑ i ∈ (Finset.univ.erase a).erase b, f i) =
      ∑ i ∈ (Finset.univ.erase a).erase b, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hfg i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1
  have hf1 := Finset.sum_erase_add (Finset.univ : Finset ι) f (Finset.mem_univ a)
  have hg1 := Finset.sum_erase_add (Finset.univ : Finset ι) g (Finset.mem_univ a)
  have hb : b ∈ (Finset.univ : Finset ι).erase a := by simp [hab.symm]
  have hf2 := Finset.sum_erase_add (Finset.univ.erase a) f hb
  have hg2 := Finset.sum_erase_add (Finset.univ.erase a) g hb
  linarith

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {k : ℕ}

theorem classSet_update_old (c : V → Fin k) (v : V) {j : Fin k} (hj : j ≠ c v) :
    classSet (Function.update c v j) (c v) = (classSet c (c v)).erase v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [hj]
  · simp [Function.update_of_ne hw, hw]

theorem classSet_update_new (c : V → Fin k) (v : V) {j : Fin k} (hj : j ≠ c v) :
    classSet (Function.update c v j) j = insert v (classSet c j) := by
  ext w
  by_cases hw : w = v
  · subst w
    simp
  · simp [Function.update_of_ne hw, hw]

theorem classSet_update_other (c : V → Fin k) (v : V) {i j : Fin k}
    (hi : i ≠ c v) (hij : i ≠ j) :
    classSet (Function.update c v j) i = classSet c i := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [hi.symm, hij.symm]
  · simp [Function.update_of_ne hw, hw]

/-- The precise edge-polynomial change, with the vector kept fixed on the
labelled vertices. This is the combinatorial input to Lemmas 2.7 and 3.6. -/
theorem RGraph.complete_classMove (c : V → Fin k) (v : V) {j : Fin k}
    (hj : j ≠ c v) (s : ℕ) (x : V → ℝ) :
    (completeOfColoring (s + 1) (Function.update c v j)).edgePolynomial x -
      (completeOfColoring (s + 1) c).edgePolynomial x =
      x v * (esymmOn ((classSet c (c v)).erase v) s x -
        esymmOn (classSet c j) s x) := by
  have hsum := sum_sub_eq_pair
    (fun i => esymmOn (classSet (Function.update c v j) i) (s + 1) x)
    (fun i => esymmOn (classSet c i) (s + 1) x) hj.symm
    (fun i hi hij => by rw [classSet_update_other c v hi hij])
  rw [classSet_update_old c v hj, classSet_update_new c v hj] at hsum
  have hvold : v ∈ classSet c (c v) := by simp
  have hvnew : v ∉ classSet c j := by simpa using hj.symm
  have hold := esymmOn_erase_succ hvold s x
  have hnew := esymmOn_insert_succ hvnew s x
  rw [complete_edgePolynomial _ (by omega), complete_edgePolynomial _ (by omega)]
  linear_combination -hsum + hold - hnew

theorem classSize_update_old (c : V → Fin k) (v : V) {j : Fin k} (hj : j ≠ c v) :
    classSize (Function.update c v j) (c v) = classSize c (c v) - 1 := by
  rw [← classSet_card, classSet_update_old c v hj,
    Finset.card_erase_of_mem (by simp : v ∈ classSet c (c v)), classSet_card]

theorem classSize_update_new (c : V → Fin k) (v : V) {j : Fin k} (hj : j ≠ c v) :
    classSize (Function.update c v j) j = classSize c j + 1 := by
  rw [← classSet_card, classSet_update_new c v hj,
    Finset.card_insert_of_notMem (by simpa using hj.symm : v ∉ classSet c j), classSet_card]

end ChromaticSpectral
