module

public import ChromaticSpectral.LocalMass
public import ChromaticSpectral.ConstantBlock
public import ChromaticSpectral.SymmetricMean

/-! # A finite vector transfer between two classes -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

variable {V : Type*} [DecidableEq V]

def localTransfer (C B : Finset V) (v : V) (x : V → ℝ) (a b : ℝ) (w : V) : ℝ :=
  if w ∈ C.erase v then a else if w ∈ insert v B then b else x w

theorem transfer_disjoint {C B : Finset V} (hCB : Disjoint C B) (v : V) :
    Disjoint (C.erase v) (insert v B) := by
  apply Finset.disjoint_left.mpr
  intro w hwC hwB
  rcases Finset.mem_insert.mp hwB with h | h
  · exact (Finset.mem_erase.mp hwC).1 h
  · exact Finset.disjoint_left.mp hCB (Finset.mem_of_mem_erase hwC) h

theorem transfer_union {C B : Finset V} {v : V} (hv : v ∈ C) :
    C.erase v ∪ insert v B = C ∪ B := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [hv]
  · simp [hw]

theorem localTransfer_left {C B : Finset V} {v w : V} {x : V → ℝ} {a b : ℝ}
    (hw : w ∈ C.erase v) : localTransfer C B v x a b w = a := by
  simp only [localTransfer, ite_eq_left hw]

theorem localTransfer_right {C B : Finset V} {v w : V} {x : V → ℝ} {a b : ℝ}
    (hCB : Disjoint C B) (hw : w ∈ insert v B) :
    localTransfer C B v x a b w = b := by
  have hwC : w ∉ C.erase v := fun h => Finset.disjoint_left.mp (transfer_disjoint hCB v) h hw
  simp only [localTransfer, ite_eq_right hwC, ite_eq_left hw]

theorem localTransfer_outside {C B : Finset V} {v w : V} {x : V → ℝ} {a b : ℝ}
    (hv : v ∈ C) (hw : w ∉ C ∪ B) : localTransfer C B v x a b w = x w := by
  have hnot : w ∉ C.erase v ∪ insert v B := by rwa [transfer_union hv]
  have hc : w ∉ C.erase v := fun h => hnot (Finset.mem_union_left _ h)
  have hb : w ∉ insert v B := fun h => hnot (Finset.mem_union_right _ h)
  simp only [localTransfer, ite_eq_right hc, ite_eq_right hb]

theorem localTransfer_nonneg {C B : Finset V} {v : V} {x : V → ℝ} {a b : ℝ}
    (hx : ∀ w, 0 ≤ x w) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ w, 0 ≤ localTransfer C B v x a b w := by
  intro w
  unfold localTransfer
  split_ifs <;> first | exact ha | exact hb | exact hx w

theorem sum_const_on {S : Finset V} {x : V → ℝ} {a : ℝ}
    (hx : ∀ w ∈ S, x w = a) : (∑ w ∈ S, x w) = (S.card : ℝ) * a := by
  rw [Finset.sum_congr rfl hx]
  simp

theorem localTransfer_sum {C B : Finset V} {v : V} (hCB : Disjoint C B)
    (hv : v ∈ C) (x : V → ℝ) (a b : ℝ) :
    (∑ w ∈ C ∪ B, localTransfer C B v x a b w) =
      ((C.erase v).card : ℝ) * a + ((insert v B).card : ℝ) * b := by
  rw [← transfer_union hv, Finset.sum_union (transfer_disjoint hCB v)]
  rw [sum_const_on (fun _ hw => localTransfer_left hw),
    sum_const_on (fun _ hw => localTransfer_right hCB hw)]

theorem esymmOn_const_on {S : Finset V} {x : V → ℝ} {a : ℝ}
    (hx : ∀ w ∈ S, x w = a) (s : ℕ) :
    esymmOn S s x = (S.card.choose s : ℝ) * a ^ s := by
  rw [esymmOn_congr hx, esymmOn_const]

variable [Fintype V]

theorem sum_eq_of_local_eq {S : Finset V} {x y : V → ℝ}
    (hout : ∀ w, w ∉ S → y w = x w)
    (hin : (∑ w ∈ S, y w) = ∑ w ∈ S, x w) : (∑ w, y w) = ∑ w, x w := by
  have hcomp : (∑ w ∈ Sᶜ, y w) = ∑ w ∈ Sᶜ, x w := by
    apply Finset.sum_congr rfl
    intro w hw
    exact hout w (Finset.mem_compl.mp hw)
  calc
    _ = (∑ w ∈ S, y w) + ∑ w ∈ Sᶜ, y w := (Finset.sum_add_sum_compl S y).symm
    _ = (∑ w ∈ S, x w) + ∑ w ∈ Sᶜ, x w := by rw [hin, hcomp]
    _ = _ := Finset.sum_add_sum_compl S x

structure LocalSmoothingWitness (C B : Finset V) (v : V) (p : ℝ) (r : ℕ)
    (x : V → ℝ) where
  y : V → ℝ
  nonneg : ∀ w, 0 ≤ y w
  outside_eq : ∀ w, w ∉ C ∪ B → y w = x w
  psum_eq : (∑ w, (y w) ^ p) = ∑ w, (x w) ^ p
  full_le : ∀ s, esymmOn (C ∪ B) s x ≤ esymmOn (C ∪ B) s y
  class_le : ∀ s, esymmOn (C.erase v) s y ≤ esymmOn C s x
  pure_lt : esymmOn (C ∪ B) r x - esymmOn C r x - esymmOn B r x <
    esymmOn (C ∪ B) r y - esymmOn (C.erase v) r y - esymmOn (insert v B) r y

end ChromaticSpectral
