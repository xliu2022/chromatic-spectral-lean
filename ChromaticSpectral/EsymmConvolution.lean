module

public import ChromaticSpectral.ElementarySymmetric

/-! # Generating polynomials and the disjoint-union convolution
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
open Polynomial
open Finset.HasAntidiagonal
namespace ChromaticSpectral
variable {V : Type*} [DecidableEq V]

noncomputable def esymmGenerating (s : Finset V) (x : V → ℝ) : ℝ[X] :=
  ∏ v ∈ s, (1 + C (x v) * X)

theorem esymmGenerating_coeff (s : Finset V) (x : V → ℝ) (j : ℕ) :
    (esymmGenerating s x).coeff j = esymmOn s j x := by
  induction s using Finset.induction generalizing j with
  | empty =>
    cases j with
    | zero => simp [esymmGenerating]
    | succ j => simp [esymmGenerating, Polynomial.coeff_one]
  | @insert v s hv ih =>
    have he : esymmGenerating (insert v s) x = esymmGenerating s x +
        C (x v) * (X * esymmGenerating s x) := by
      unfold esymmGenerating
      rw [Finset.prod_insert hv]
      ring
    rw [he, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    cases j with
    | zero => simp [ih]
    | succ j =>
      rw [Polynomial.coeff_X_mul, ih, ih, esymmOn_insert_succ hv]

theorem esymmOn_disjoint_union {s t : Finset V} (hst : Disjoint s t)
    (j : ℕ) (x : V → ℝ) :
    esymmOn (s ∪ t) j x = ∑ ab ∈ antidiagonal j,
      esymmOn s ab.1 x * esymmOn t ab.2 x := by
  have hp : esymmGenerating (s ∪ t) x = esymmGenerating s x * esymmGenerating t x :=
    Finset.prod_union hst
  rw [← esymmGenerating_coeff, hp, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab _
  rw [esymmGenerating_coeff, esymmGenerating_coeff]

theorem esymmOn_disjoint_union_range {s t : Finset V} (hst : Disjoint s t)
    (j : ℕ) (x : V → ℝ) :
    esymmOn (s ∪ t) j x = ∑ i ∈ Finset.range (j + 1),
      esymmOn s i x * esymmOn t (j - i) x := by
  rw [esymmOn_disjoint_union hst,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem esymmOn_union_difference {s s' t : Finset V} (hst : Disjoint s t)
    (hs't : Disjoint s' t) (r : ℕ) {x y : V → ℝ} (ht : ∀ w ∈ t, y w = x w) :
    esymmOn (s' ∪ t) r y - esymmOn (s ∪ t) r x =
      (esymmOn s' r y - esymmOn s r x) +
        ∑ i ∈ Finset.range r, (esymmOn s' i y - esymmOn s i x) * esymmOn t (r - i) x := by
  have ht' (d : ℕ) := esymmOn_congr ht d
  calc
    _ = ∑ i ∈ Finset.range (r + 1),
        (esymmOn s' i y - esymmOn s i x) * esymmOn t (r - i) x := by
      rw [esymmOn_disjoint_union_range hs't, esymmOn_disjoint_union_range hst,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [ht']
      ring
    _ = _ := by
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, esymmOn_zero, mul_one]
      ring

end ChromaticSpectral
