module

public import ChromaticSpectral.BalancedPartitions
public import ChromaticSpectral.BinomialJensen
public import ChromaticSpectral.ClassLocalization
public import ChromaticSpectral.SpectralTransfer

/-!
# The explicit spectral bound for balanced complete colourings

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r k : ℕ}

theorem BalancedColoring.sum_classSize_apply {c : V → Fin k} (hc : BalancedColoring c)
    (hk : 0 < k) (f : ℕ → ℝ) :
    ∑ i, f (classSize c i) =
      (Fintype.card V % k : ℕ) * f (Fintype.card V / k + 1) +
        ((k - Fintype.card V % k : ℕ) : ℝ) * f (Fintype.card V / k) := by
  have hi (i : Fin k) : f (classSize c i) =
      twoLevelWeights (largeClasses c) (f (Fintype.card V / k + 1)) (f (Fintype.card V / k)) i := by
    unfold twoLevelWeights
    by_cases hi : i ∈ largeClasses c
    · rw [if_pos hi, (mem_largeClasses c i).mp hi]
    · rw [if_neg hi]
      have hs := hc.classSize_eq_floor_or_succ hk i
      have hn := (mem_largeClasses c i).not.mp hi
      rw [hs.resolve_right hn]
  calc
    _ = ∑ i : Fin k, twoLevelWeights (largeClasses c)
        (f (Fintype.card V / k + 1)) (f (Fintype.card V / k)) i :=
      Finset.sum_congr rfl (fun i _ => hi i)
    _ = _ := by
      rw [sum_twoLevel_apply Finset.univ (largeClasses c) (Finset.subset_univ _) (fun z => z),
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        hc.card_largeClasses hk]

theorem BalancedColoring.floor_ge {c : V → Fin k} (hc : BalancedColoring c)
    (hk : 0 < k) (hN : (r - 1) * k < Fintype.card V) :
    r - 1 ≤ Fintype.card V / k := by
  exact (Nat.le_div_iff_mul_le hk).2 hN.le

theorem RGraph.complete_edges_nonempty_of_classSize_pos (c : V → Fin k)
    (hk : 2 ≤ k) (hr : 2 ≤ r) (hN : r ≤ Fintype.card V)
    (hsize : ∀ i, 0 < classSize c i) : (completeOfColoring r c).edges.Nonempty := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (classSet c i).card from hsize i)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (classSet c j).card from hsize j)
  have hcu := (mem_classSet c i u).mp hu
  have hcv := (mem_classSet c j v).mp hv
  have huv : u ≠ v := by intro h; apply hij; simpa [hcu, hcv] using congrArg c h
  obtain ⟨e, hpair, heU, hecard⟩ := Finset.exists_subsuperset_card_eq
    (s := ({u, v} : Finset V)) (t := Finset.univ) (Finset.subset_univ _)
    (by simpa [huv] using hr) (by simpa using hN)
  refine ⟨e, (mem_completeOfColoring c e).mpr ⟨hecard, u, hpair (by simp), v, hpair (by simp), ?_⟩⟩
  simpa only [hcu, hcv] using hij

theorem BalancedColoring.complete_edges_nonempty {c : V → Fin k} (hc : BalancedColoring c)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hN : (r - 1) * k < Fintype.card V) :
    (RGraph.completeOfColoring r c).edges.Nonempty := by
  have hk0 : 0 < k := by omega
  have hq := hc.floor_ge hk0 hN
  apply RGraph.complete_edges_nonempty_of_classSize_pos c hk (by omega)
  · have hmul := Nat.mul_le_mul_left (r - 1) (show 1 ≤ k by omega)
    simp only [Nat.mul_one] at hmul
    omega
  · intro i
    have hi := (hc.classSize_bounds hk0 i).1
    omega

/-- The exact edge-count formula in Lemma 6.1. -/
theorem RGraph.balanced_complete_edge_count (c : V → Fin k) (hc : BalancedColoring c)
    (hk : 0 < k) (hr : 0 < r) :
    ((completeOfColoring r c).edges.card : ℝ) = ((Fintype.card V).choose r : ℝ) -
      (Fintype.card V % k : ℕ) * ((Fintype.card V / k + 1).choose r : ℝ) -
      ((k - Fintype.card V % k : ℕ) : ℝ) * ((Fintype.card V / k).choose r : ℝ) := by
  rw [complete_edge_count c hr, hc.sum_classSize_apply hk (fun n => (n.choose r : ℝ))]
  ring

/-- The generalized-binomial upper bound for the edge count. -/
theorem RGraph.balanced_complete_edge_count_le (c : V → Fin k) (hc : BalancedColoring c)
    (hr : 3 ≤ r) (hk : 0 < k) (hN : (r - 1) * k < Fintype.card V) :
    ((completeOfColoring r c).edges.card : ℝ) ≤ ((Fintype.card V).choose r : ℝ) -
      (k : ℝ) * Ring.choose ((Fintype.card V : ℝ) / k) r := by
  have h := balanced_binomial_jensen_le r k (Fintype.card V / k) (Fintype.card V % k)
    hr hk (hc.floor_ge hk hN) (Nat.mod_lt _ hk)
  rw [Nat.div_add_mod] at h
  rw [balanced_complete_edge_count c hc hk (by omega)]
  linarith

theorem RGraph.balanced_complete_edge_count_eq_iff (c : V → Fin k) (hc : BalancedColoring c)
    (hr : 3 ≤ r) (hk : 0 < k) (hN : (r - 1) * k < Fintype.card V) :
    ((completeOfColoring r c).edges.card : ℝ) = ((Fintype.card V).choose r : ℝ) -
        (k : ℝ) * Ring.choose ((Fintype.card V : ℝ) / k) r ↔ k ∣ Fintype.card V := by
  have h := balanced_binomial_jensen_eq_iff r k (Fintype.card V / k) (Fintype.card V % k)
    hr hk (hc.floor_ge hk hN) (Nat.mod_lt _ hk)
  rw [Nat.div_add_mod] at h
  rw [balanced_complete_edge_count c hc hk (by omega), Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro he
    exact h.mp (by linarith)
  · intro ht
    have he := h.mpr ht
    linarith

theorem RGraph.balanced_complete_twoLevel_polynomial (c : V → Fin k) (hc : BalancedColoring c)
    (hk : 0 < k) (hr : 0 < r) (a b : ℝ) :
    (completeOfColoring r c).edgePolynomial (twoLevelWeights (largeVertices c) a b) =
      esymmOn Finset.univ r (twoLevelWeights (largeVertices c) a b) -
      (Fintype.card V % k : ℕ) * ((Fintype.card V / k + 1).choose r : ℝ) * a ^ r -
      ((k - Fintype.card V % k : ℕ) : ℝ) * ((Fintype.card V / k).choose r : ℝ) * b ^ r := by
  have he (i : Fin k) : esymmOn (classSet c i) r (twoLevelWeights (largeVertices c) a b) =
      (classSize c i).choose r * (if classSize c i = Fintype.card V / k + 1 then a else b) ^ r := by
    calc
      _ = esymmOn (classSet c i) r
          (fun _ => if classSize c i = Fintype.card V / k + 1 then a else b) := by
        apply esymmOn_congr
        intro v hv
        have hcv := (mem_classSet c i v).mp hv
        simp only [twoLevelWeights, mem_largeVertices, hcv]
      _ = _ := by rw [esymmOn_const, classSet_card]
  rw [complete_edgePolynomial c hr]
  have hs : (∑ i, esymmOn (classSet c i) r (twoLevelWeights (largeVertices c) a b)) =
      (Fintype.card V % k : ℕ) * ((Fintype.card V / k + 1).choose r : ℝ) * a ^ r +
      ((k - Fintype.card V % k : ℕ) : ℝ) * ((Fintype.card V / k).choose r : ℝ) * b ^ r := by
    simp_rw [he]
    rw [hc.sum_classSize_apply hk (fun n => (n.choose r : ℝ) *
      (if n = Fintype.card V / k + 1 then a else b) ^ r)]
    simp only [if_pos rfl, if_neg (show Fintype.card V / k ≠ Fintype.card V / k + 1 by omega), ite_true]
    ring
  rw [hs]
  ring

theorem RGraph.balanced_complete_lagrangian_lt_of_not_dvd (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) (hd : ¬ k ∣ Fintype.card V) :
    (completeOfColoring r c).pSpectralRadius 1 < explicitBound r k (Fintype.card V) 1 := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hk0 : 0 < k := by omega
  have hq := hc.floor_ge hk0 hN
  have ht : 0 < Fintype.card V % k := Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
  have htk := Nat.mod_lt (Fintype.card V) hk0
  have hQ := hc.complete_edges_nonempty (by omega) hk hN
  obtain ⟨x, hx⟩ := (completeOfColoring r c).exists_maximizer zero_lt_one
  have hpos := complete_maximizer_pos (by omega) c (by norm_num) hQ hx
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (largeVertices c).card by
    rw [hc.card_largeVertices hk0]
    positivity)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (show 0 < ((Finset.univ : Finset V) \ largeVertices c).card by
      rw [hc.card_smallVertices hk0]
      exact Nat.mul_pos (Nat.sub_pos_of_lt htk) (by omega))
  have huq := (mem_largeVertices c u).mp hu
  have hvn := (Finset.mem_sdiff.mp hv).2
  have hvq : classSize c (c v) = Fintype.card V / k :=
    (hc.classSize_eq_floor_or_succ hk0 (c v)).resolve_right ((mem_largeVertices c v).not.mp hvn)
  have hab : x u ≤ x v := complete_maximizer_weight_antitone (by omega) c hQ hx
    (show classSize c (c v) ≤ classSize c (c u) by rw [huq, hvq]; omega)
  have hba := complete_maximizer_adjacent_class_ratio hr c hQ hx hq huq hvq
  have hvec : x = twoLevelWeights (largeVertices c) (x u) (x v) := by
    funext w
    unfold twoLevelWeights
    by_cases hw : w ∈ largeVertices c
    · rw [if_pos hw]
      apply complete_maximizer_equal_of_classSize_eq (by omega) c hQ hx
      rw [(mem_largeVertices c w).mp hw, huq]
    · rw [if_neg hw]
      apply complete_maximizer_equal_of_classSize_eq (by omega) c hQ hx
      rw [(hc.classSize_eq_floor_or_succ hk0 (c w)).resolve_right
        ((mem_largeVertices c w).not.mp hw), hvq]
  have hsum : ∑ w ∈ (Finset.univ : Finset V), twoLevelWeights (largeVertices c) (x u) (x v) w = 1 := by
    rw [← hvec]
    simpa only [Real.rpow_one] using hx.1.2
  have hB := twoLevel_explicit_strict_bound Finset.univ (largeVertices c) (Finset.subset_univ _)
    r k (Fintype.card V / k) (Fintype.card V % k) hr hk hq ht htk
    (hc.card_largeVertices hk0) (hc.card_smallVertices hk0) (hpos u) hab hba hsum
  have hE : (completeOfColoring r c).edgePolynomial x <
      (((Fintype.card V).choose r : ℝ) - (k : ℝ) * Ring.choose ((Fintype.card V : ℝ) / k) r) /
        (Fintype.card V : ℝ) ^ r := by
    rw [hvec, balanced_complete_twoLevel_polynomial c hc hk0 (by omega)]
    simpa only [Finset.card_univ] using hB
  rw [explicitBound_one, ← hx.2, polyform]
  simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hE (by positivity : (0 : ℝ) < r.factorial)

theorem RGraph.balanced_complete_lagrangian_eq_of_dvd (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) (hd : k ∣ Fintype.card V) :
    (completeOfColoring r c).pSpectralRadius 1 = explicitBound r k (Fintype.card V) 1 := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hk0 : 0 < k := by omega
  have hN0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ht := Nat.mod_eq_zero_of_dvd hd
  have hlarge : largeClasses c = ∅ := Finset.card_eq_zero.mp (by rw [hc.card_largeClasses hk0, ht])
  have hsize (i : Fin k) : classSize c i = Fintype.card V / k := by
    apply (hc.classSize_eq_floor_or_succ hk0 i).resolve_right
    intro hi
    have hh := (mem_largeClasses c i).mpr hi
    simpa [hlarge] using hh
  have hQ := hc.complete_edges_nonempty hr hk hN
  obtain ⟨x, hx⟩ := (completeOfColoring r c).exists_maximizer zero_lt_one
  let v : V := Classical.arbitrary V
  have heq (w : V) : x w = x v := complete_maximizer_equal_of_classSize_eq hr c hQ hx
    (by rw [hsize, hsize])
  have hsum : (Fintype.card V : ℝ) * x v = 1 := by
    calc
      _ = ∑ w : V, x v := by simp
      _ = ∑ w : V, x w := Finset.sum_congr rfl (fun w _ => (heq w).symm)
      _ = 1 := by simpa only [Real.rpow_one] using hx.1.2
  have hv : x v = 1 / (Fintype.card V : ℝ) := by
    apply (eq_div_iff hN0.ne').2
    nlinarith only [hsum]
  have hconst : x = fun _ => 1 / (Fintype.card V : ℝ) := funext (fun w => (heq w).trans hv)
  have hcard := (balanced_complete_edge_count_eq_iff c hc hr hk0 hN).mpr hd
  rw [← hx.2, hconst, polyform, edgePolynomial_const, hcard, explicitBound_one, one_div_pow]
  ring

/-- Proposition 6.2. -/
theorem RGraph.balanced_complete_lagrangian_le (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) :
    (completeOfColoring r c).pSpectralRadius 1 ≤ explicitBound r k (Fintype.card V) 1 := by
  by_cases hd : k ∣ Fintype.card V
  · exact (balanced_complete_lagrangian_eq_of_dvd c hc (by omega) hk hN hd).le
  · exact (balanced_complete_lagrangian_lt_of_not_dvd c hc hr hk hN hd).le

theorem BalancedColoring.explicit_coefficient_pos {c : V → Fin k}
    (hc : BalancedColoring c) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) :
    0 < ((Fintype.card V).choose r : ℝ) -
      (k : ℝ) * Ring.choose ((Fintype.card V : ℝ) / k) r := by
  have hQ := hc.complete_edges_nonempty hr hk hN
  have hcard : (0 : ℝ) < (RGraph.completeOfColoring r c).edges.card := by
    exact_mod_cast hQ.card_pos
  exact lt_of_lt_of_le hcard (RGraph.balanced_complete_edge_count_le c hc hr (by omega) hN)

theorem RGraph.balanced_complete_spectral_explicit_le (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) {p : ℝ} (hp : 1 ≤ p) :
    (completeOfColoring r c).pSpectralRadius p ≤ explicitBound r k (Fintype.card V) p := by
  let C : ℝ := ((Fintype.card V).choose r : ℝ) -
    (k : ℝ) * Ring.choose ((Fintype.card V : ℝ) / k) r
  let A : ℝ := (r.factorial : ℝ) * C
  have hC : 0 < C := hc.explicit_coefficient_pos (by omega) hk hN
  have hA : 0 < A := mul_pos (by positivity) hC
  have hN0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have he : (r.factorial : ℝ) * (completeOfColoring r c).edges.card ≤ A :=
    mul_le_mul_of_nonneg_left (balanced_complete_edge_count_le c hc (by omega) (by omega) hN)
      (by positivity)
  have hL : (completeOfColoring r c).pSpectralRadius 1 ≤
      A * (Fintype.card V : ℝ) ^ (-(r : ℝ)) := by
    simpa only [explicitBound, div_one, A, C] using balanced_complete_lagrangian_le c hc hr hk hN
  exact (completeOfColoring r c).pSpectralRadius_le_scaled_of_lagrangian_le hp hA hN0 he hL

theorem RGraph.balanced_complete_spectral_explicit_lt_of_not_dvd (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) (hd : ¬ k ∣ Fintype.card V)
    {p : ℝ} (hp : 1 ≤ p) :
    (completeOfColoring r c).pSpectralRadius p < explicitBound r k (Fintype.card V) p := by
  let C : ℝ := ((Fintype.card V).choose r : ℝ) -
    (k : ℝ) * Ring.choose ((Fintype.card V : ℝ) / k) r
  let A : ℝ := (r.factorial : ℝ) * C
  have hC : 0 < C := hc.explicit_coefficient_pos (by omega) hk hN
  have hA : 0 < A := mul_pos (by positivity) hC
  have hN0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have he : (r.factorial : ℝ) * (completeOfColoring r c).edges.card ≤ A :=
    mul_le_mul_of_nonneg_left (balanced_complete_edge_count_le c hc (by omega) (by omega) hN)
      (by positivity)
  have hL : (completeOfColoring r c).pSpectralRadius 1 <
      A * (Fintype.card V : ℝ) ^ (-(r : ℝ)) := by
    simpa only [explicitBound, div_one, A, C] using
      balanced_complete_lagrangian_lt_of_not_dvd c hc hr hk hN hd
  exact (completeOfColoring r c).pSpectralRadius_lt_scaled_of_lagrangian_lt hp hA hN0 he hL

theorem RGraph.balanced_complete_spectral_explicit_eq_of_dvd (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) (hd : k ∣ Fintype.card V)
    {p : ℝ} (hp : 1 ≤ p) :
    (completeOfColoring r c).pSpectralRadius p = explicitBound r k (Fintype.card V) p := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  apply le_antisymm (balanced_complete_spectral_explicit_le c hc hr hk hN hp)
  have h := (completeOfColoring r c).uniform_spectral_lower (lt_of_lt_of_le zero_lt_one hp)
  rw [(balanced_complete_edge_count_eq_iff c hc (by omega) (by omega) hN).mpr hd] at h
  exact h

theorem RGraph.balanced_complete_spectral_explicit_eq_iff (c : V → Fin k)
    (hc : BalancedColoring c) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hN : (r - 1) * k < Fintype.card V) {p : ℝ} (hp : 1 ≤ p) :
    (completeOfColoring r c).pSpectralRadius p = explicitBound r k (Fintype.card V) p ↔
      k ∣ Fintype.card V := by
  constructor
  · intro he
    by_contra hd
    exact (balanced_complete_spectral_explicit_lt_of_not_dvd c hc hr hk hN hd hp).ne he
  · intro hd
    exact balanced_complete_spectral_explicit_eq_of_dvd c hc hr hk hN hd hp

/-- Theorem 1.4 of Liu--Luo, including all real `p ≥ 1` and the exact equality case. -/
theorem theorem_1_4 (G : RGraph V r) (hG : G.IsBalancedComplete k)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hN : (r - 1) * k < Fintype.card V)
    {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p ≤ explicitBound r k (Fintype.card V) p ∧
      (G.pSpectralRadius p = explicitBound r k (Fintype.card V) p ↔ k ∣ Fintype.card V) := by
  obtain ⟨c, hc, rfl⟩ := hG
  exact ⟨RGraph.balanced_complete_spectral_explicit_le c hc hr hk hN hp,
    RGraph.balanced_complete_spectral_explicit_eq_iff c hc hr hk hN hp⟩

end ChromaticSpectral
