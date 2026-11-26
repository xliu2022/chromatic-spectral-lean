module

public import ChromaticSpectral.Isomorphism

/-! # The sizes and uniqueness of balanced colour partitions

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

universe u v
variable {V : Type u} [DecidableEq V] [Fintype V] {k : ℕ}

noncomputable def largeClasses (c : V → Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun i => classSize c i = Fintype.card V / k + 1

noncomputable def largeVertices (c : V → Fin k) : Finset V :=
  Finset.univ.filter fun v => classSize c (c v) = Fintype.card V / k + 1

@[simp] theorem mem_largeClasses (c : V → Fin k) (i : Fin k) :
    i ∈ largeClasses c ↔ classSize c i = Fintype.card V / k + 1 := by
  simp [largeClasses]

@[simp] theorem mem_largeVertices (c : V → Fin k) (v : V) :
    v ∈ largeVertices c ↔ classSize c (c v) = Fintype.card V / k + 1 := by
  simp [largeVertices]

theorem BalancedColoring.classSize_bounds {c : V → Fin k} (hc : BalancedColoring c)
    (hk : 0 < k) (i : Fin k) :
    Fintype.card V / k ≤ classSize c i ∧ classSize c i ≤ Fintype.card V / k + 1 := by
  have hdiv := Nat.mod_add_div (Fintype.card V) k
  have hmod := Nat.mod_lt (Fintype.card V) hk
  constructor
  · by_contra hh
    have hi : classSize c i < Fintype.card V / k := lt_of_not_ge hh
    have hle (j : Fin k) (_ : j ∈ (Finset.univ : Finset (Fin k))) :
        classSize c j ≤ Fintype.card V / k := by have := hc j i; omega
    have hsum := Finset.sum_lt_sum hle ⟨i, Finset.mem_univ i, hi⟩
    rw [classSize_sum] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega
  · by_contra hh
    have hi : Fintype.card V / k + 1 < classSize c i := lt_of_not_ge hh
    have hle (j : Fin k) (_ : j ∈ (Finset.univ : Finset (Fin k))) :
        Fintype.card V / k + 1 ≤ classSize c j := by have := hc i j; omega
    have hsum := Finset.sum_le_sum hle
    rw [classSize_sum] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_add, Nat.mul_one] at hsum
    omega

theorem BalancedColoring.classSize_eq_floor_or_succ {c : V → Fin k}
    (hc : BalancedColoring c) (hk : 0 < k) (i : Fin k) :
    classSize c i = Fintype.card V / k ∨ classSize c i = Fintype.card V / k + 1 := by
  have h := hc.classSize_bounds hk i
  omega

theorem BalancedColoring.card_largeClasses {c : V → Fin k}
    (hc : BalancedColoring c) (hk : 0 < k) :
    (largeClasses c).card = Fintype.card V % k := by
  have hsize (i : Fin k) : classSize c i = Fintype.card V / k +
      if classSize c i = Fintype.card V / k + 1 then 1 else 0 := by
    have h := hc.classSize_eq_floor_or_succ hk i
    split_ifs <;> omega
  have hsum : Fintype.card V = k * (Fintype.card V / k) + (largeClasses c).card := by
    calc
      _ = ∑ i, classSize c i := (classSize_sum c).symm
      _ = ∑ i : Fin k, (Fintype.card V / k +
          if classSize c i = Fintype.card V / k + 1 then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => hsize i
      _ = k * (Fintype.card V / k) + (largeClasses c).card := by
        simp [Finset.sum_add_distrib, largeClasses]
  have hdiv := Nat.mod_add_div (Fintype.card V) k
  omega

theorem card_largeVertices_eq (c : V → Fin k) :
    (largeVertices c).card = (largeClasses c).card * (Fintype.card V / k + 1) := by
  have hh := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V)
    (largeClasses c) c
  have he : (Finset.univ.filter fun v => c v ∈ largeClasses c) = largeVertices c := by
    ext v
    simp
  rw [he] at hh
  rw [← hh]
  apply Finset.sum_const_nat
  intro i hi
  exact (mem_largeClasses c i).mp hi

theorem BalancedColoring.card_largeVertices {c : V → Fin k}
    (hc : BalancedColoring c) (hk : 0 < k) :
    (largeVertices c).card = (Fintype.card V % k) * (Fintype.card V / k + 1) := by
  rw [card_largeVertices_eq, hc.card_largeClasses hk]

theorem BalancedColoring.card_smallVertices {c : V → Fin k}
    (hc : BalancedColoring c) (hk : 0 < k) :
    ((Finset.univ : Finset V) \ largeVertices c).card =
      (k - Fintype.card V % k) * (Fintype.card V / k) := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    hc.card_largeVertices hk]
  have hmod : Fintype.card V % k ≤ k := (Nat.mod_lt _ hk).le
  have hmul := Nat.mul_le_mul_right (Fintype.card V / k) hmod
  have hdiv := Nat.mod_add_div (Fintype.card V) k
  have he : Fintype.card V =
      (Fintype.card V % k) * (Fintype.card V / k + 1) +
        (k - Fintype.card V % k) * (Fintype.card V / k) := by
    rw [Nat.sub_mul, Nat.mul_add, Nat.mul_one]
    omega
  omega

end ChromaticSpectral
