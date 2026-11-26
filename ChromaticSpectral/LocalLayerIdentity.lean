module

public import ChromaticSpectral.EsymmConvolution
public import ChromaticSpectral.LocalMass

/-! # Identifying the pure crossing layer with the local symmetric-sum deficit
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
variable {V : Type*} [DecidableEq V]

theorem esymmOn_of_constant {s : Finset V} {x : V → ℝ} {a : ℝ}
    (hx : ∀ w ∈ s, x w = a) (j : ℕ) :
    esymmOn s j x = (s.card.choose j : ℝ) * a ^ j := by
  rw [esymmOn_congr hx, esymmOn_const]

theorem crossLayer_eq_esymm_sub {C B : Finset V} (hCB : Disjoint C B)
    {x : V → ℝ} {a b : ℝ} (hC : ∀ w ∈ C, x w = a) (hB : ∀ w ∈ B, x w = b)
    {r : ℕ} (hr : 0 < r) :
    crossLayer C.card B.card r a b =
      esymmOn (C ∪ B) r x - esymmOn C r x - esymmOn B r x := by
  rw [esymmOn_disjoint_union_range hCB]
  simp_rw [esymmOn_of_constant hC, esymmOn_of_constant hB]
  have hsum : (∑ i ∈ Finset.range (r + 1),
      ((C.card.choose i : ℝ) * a ^ i) * ((B.card.choose (r - i) : ℝ) * b ^ (r - i))) =
      ∑ i ∈ Finset.range (r + 1),
        (C.card.choose i : ℝ) * (B.card.choose (r - i) : ℝ) * a ^ i * b ^ (r - i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Finset.sum_range_succ, crossLayer, Finset.sum_Ico_eq_sub _ hr]
  simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    Nat.sub_zero, Nat.sub_self, one_mul, mul_one]
  ring

end ChromaticSpectral
