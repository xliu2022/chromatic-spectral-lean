module

public import ChromaticSpectral.BalancedPartitions

/-! # Isomorphism between complete hypergraphs with balanced colour classes

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

universe u v
variable {V : Type u} {W : Type v}
variable [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] {r k : ℕ}

theorem BalancedColoring.card_classSize_fiber {c : V → Fin k}
    (hc : BalancedColoring c) (hk : 0 < k) (n : ℕ) :
    (Finset.univ.filter fun i => classSize c i = n).card =
      if n = Fintype.card V / k + 1 then Fintype.card V % k
      else if n = Fintype.card V / k then k - Fintype.card V % k else 0 := by
  split_ifs with hn1 hn0
  · subst n
    exact hc.card_largeClasses hk
  · subst n
    have he : (Finset.univ.filter fun i => classSize c i = Fintype.card V / k) =
        Finset.univ \ largeClasses c := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        mem_largeClasses]
      have h := hc.classSize_eq_floor_or_succ hk i
      omega
    rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hc.card_largeClasses hk]
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    have h := hc.classSize_eq_floor_or_succ hk i
    omega

theorem exists_colorPreservingEquiv_of_classSize (c : V → Fin k) (d : W → Fin k)
    (g : Fin k ≃ Fin k) (hsize : ∀ i, classSize c i = classSize d (g i)) :
    ∃ f : V ≃ W, ∀ v, d (f v) = g (c v) := by
  classical
  let E (i : Fin k) : {v // c v = i} ≃ {w // d w = g i} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype, classSize] using hsize i)
  let f : V ≃ W := (Equiv.sigmaFiberEquiv c).symm.trans
    ((Equiv.sigmaCongr g E).trans (Equiv.sigmaFiberEquiv d))
  refine ⟨f, ?_⟩
  intro v
  exact (E (c v) ⟨v, rfl⟩).property

theorem BalancedColoring.exists_classSize_equiv (c : V → Fin k) (d : W → Fin k)
    (hc : BalancedColoring c) (hd : BalancedColoring d)
    (hcard : Fintype.card V = Fintype.card W) (hk : 0 < k) :
    ∃ g : Fin k ≃ Fin k, ∀ i, classSize c i = classSize d (g i) := by
  classical
  have hfiber (n : ℕ) :
      Fintype.card {i : Fin k // classSize c i = n} =
        Fintype.card {i : Fin k // classSize d i = n} := by
    rw [Fintype.card_subtype, Fintype.card_subtype,
      hc.card_classSize_fiber hk, hd.card_classSize_fiber hk, hcard]
  let E (n : ℕ) : {i : Fin k // classSize c i = n} ≃
      {i : Fin k // classSize d i = n} := Fintype.equivOfCardEq (hfiber n)
  refine ⟨Equiv.ofFiberEquiv E, ?_⟩
  intro i
  exact (Equiv.ofFiberEquiv_map E i).symm

theorem RGraph.balanced_complete_isomorphic (c : V → Fin k) (d : W → Fin k)
    (hc : BalancedColoring c) (hd : BalancedColoring d)
    (hcard : Fintype.card V = Fintype.card W) (hk : 0 < k) :
    (completeOfColoring r c).IsIsomorphic (completeOfColoring r d) := by
  obtain ⟨g, hg⟩ := hc.exists_classSize_equiv c d hd hcard hk
  obtain ⟨f, hf⟩ := exists_colorPreservingEquiv_of_classSize c d g hg
  exact complete_isomorphic_of_color_equiv c d f g hf

end ChromaticSpectral
