module

public import ChromaticSpectral.ChooseConvexity
public import ChromaticSpectral.Endpoint
public import ChromaticSpectral.SymmetricMean

/-!
# Bernstein coefficients for the explicit Lagrangian bound

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

variable {V : Type*} [DecidableEq V]

def twoLevelWeights (u : Finset V) (a b : ℝ) (v : V) : ℝ :=
  if v ∈ u then a else b

theorem esymmOn_sum_powersetCard (s : Finset V) (x : V → ℝ) {r m : ℕ}
    (hm : m ≤ r) :
    ∑ e ∈ s.powersetCard r, esymmOn e m x =
      ((s.card - m).choose (r - m) : ℝ) * esymmOn s m x := by
  have he : ∀ e ∈ s.powersetCard r,
      e.powersetCard m = (s.powersetCard m).filter (fun t => t ⊆ e) := by
    intro e he
    ext t
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    have hes := (Finset.mem_powersetCard.mp he).1
    exact ⟨fun h => ⟨⟨h.1.trans hes, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  simp_rw [esymmOn]
  calc
    _ = ∑ e ∈ s.powersetCard r,
        ∑ t ∈ s.powersetCard m, if t ⊆ e then ∏ v ∈ t, x v else 0 := by
      apply Finset.sum_congr rfl
      intro e he'
      rw [he e he', Finset.sum_filter]
    _ = ∑ t ∈ s.powersetCard m,
        ∑ e ∈ s.powersetCard r, if t ⊆ e then ∏ v ∈ t, x v else 0 :=
      Finset.sum_comm
    _ = ∑ t ∈ s.powersetCard m,
        ((s.card - m).choose (r - m) : ℝ) * ∏ v ∈ t, x v := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨hts, htm⟩ := Finset.mem_powersetCard.mp ht
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        Finset.card_filter_powersetCard_subset t s r hts (by omega), htm]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem prod_affine_eq_sum_esymm (s : Finset V) (x : V → ℝ) (a b : ℝ) :
    ∏ v ∈ s, (a + b * x v) =
      ∑ m ∈ Finset.range (s.card + 1), a ^ (s.card - m) * b ^ m * esymmOn s m x := by
  rw [show (fun v => a + b * x v) = (fun v => b * x v + a) by funext v; ring,
    Finset.prod_add, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro m hm
  rw [esymmOn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨hts, htm⟩ := Finset.mem_powersetCard.mp ht
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset hts, htm]
  ring

theorem esymmOn_affine (s : Finset V) (x : V → ℝ) (a b : ℝ) (r : ℕ) :
    esymmOn s r (fun v => a + b * x v) =
      ∑ m ∈ Finset.range (r + 1),
        ((s.card - m).choose (r - m) : ℝ) * a ^ (r - m) * b ^ m * esymmOn s m x := by
  unfold esymmOn
  calc
    _ = ∑ e ∈ s.powersetCard r,
        ∑ m ∈ Finset.range (r + 1), a ^ (r - m) * b ^ m * esymmOn e m x := by
      apply Finset.sum_congr rfl
      intro e he
      rw [prod_affine_eq_sum_esymm, (Finset.mem_powersetCard.mp he).2]
    _ = ∑ m ∈ Finset.range (r + 1), a ^ (r - m) * b ^ m *
        (∑ e ∈ s.powersetCard r, esymmOn e m x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [esymmOn_sum_powersetCard s x (by have := Finset.mem_range.mp hm; omega)]
      simp only [esymmOn]
      ring

theorem choose_convex_jensen_strict (r m : ℕ) (hr : 3 ≤ r) (hm : m ≤ r - 1)
    {q α : ℝ} (hq : (r : ℝ) - 1 ≤ q) (hα : 0 < α) (hα1 : α < 1) :
    Ring.choose (q + α) r / (q + α) ^ m <
      (1 - α) * (Ring.choose q r / q ^ m) +
        α * (Ring.choose (q + 1) r / (q + 1) ^ m) := by
  have h := (realChoose_div_pow_strictConvex r m hr hm).2 hq
    (show (q + 1) ∈ Set.Ici ((r : ℝ) - 1) by simp only [Set.mem_Ici]; linarith)
    (show q ≠ q + 1 by linarith) (sub_pos.mpr hα1) hα (by ring)
  simpa only [smul_eq_mul, show (1 - α) * q + α * (q + 1) = q + α by ring] using h

theorem choose_convex_jensen_scaled (r m : ℕ) (hr : 3 ≤ r) (hm : m ≤ r - 1)
    {q α k : ℝ} (hq : (r : ℝ) - 1 ≤ q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) :
    k * Ring.choose (q + α) r * ((q + 1) / (q + α)) ^ m <
      k * α * Ring.choose (q + 1) r +
        k * (1 - α) * Ring.choose q r * ((q + 1) / q) ^ m := by
  have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hν : 0 < q + α := by positivity
  have h := mul_lt_mul_of_pos_right (choose_convex_jensen_strict r m hr hm hq hα hα1)
    (show 0 < k * (q + 1) ^ m by positivity)
  convert! h using 1 <;> rw [div_pow] <;>
    field_simp [hq0.ne', hq1.ne', hν.ne'] <;> ring

noncomputable def bernsteinDeficitCoeff (s : Finset V) (θ : V → ℝ) (r m : ℕ)
    (C L U W ρ : ℝ) : ℝ :=
  (r.choose m : ℝ) * (C * L ^ m + U + W * ρ ^ m) -
    ((s.card - m).choose (r - m) : ℝ) * esymmOn s m θ

theorem bernsteinDeficitCoeff_lower (s : Finset V) (θ : V → ℝ) (r m : ℕ)
    (hm : m ≤ r) (hθ : ∀ v ∈ s, 0 ≤ θ v) (C U W ρ : ℝ) :
    (r.choose m : ℝ) *
        ((C - (s.card.choose r : ℝ)) * ((∑ v ∈ s, θ v) / s.card) ^ m + U + W * ρ ^ m) ≤
      bernsteinDeficitCoeff s θ r m C ((∑ v ∈ s, θ v) / s.card) U W ρ := by
  have h := mul_le_mul_of_nonneg_left (esymmOn_le_choose_mul_mean_pow hθ m)
    (show (0 : ℝ) ≤ (s.card - m).choose (r - m) by positivity)
  have hb : ((s.card - m).choose (r - m) : ℝ) * (s.card.choose m : ℝ) =
      (s.card.choose r : ℝ) * (r.choose m : ℝ) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_mul (n := s.card) hm)
    push_cast at h
    nlinarith only [h]
  unfold bernsteinDeficitCoeff
  rw [← mul_assoc, hb] at h
  nlinarith only [h]

theorem bernsteinDeficitCoeff_pos_before_last (s : Finset V) (θ : V → ℝ)
    (r m : ℕ) (hr : 3 ≤ r) (hm : m < r) (hθ : ∀ v ∈ s, 0 ≤ θ v)
    {q α k : ℝ} (hq : (r : ℝ) - 1 ≤ q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k)
    (hmean : (∑ v ∈ s, θ v) / s.card = (q + 1) / (q + α)) :
    0 < bernsteinDeficitCoeff s θ r m
      ((s.card.choose r : ℝ) - k * Ring.choose (q + α) r)
      ((q + 1) / (q + α))
      (k * α * Ring.choose (q + 1) r)
      (k * (1 - α) * Ring.choose q r) ((q + 1) / q) := by
  have hj := choose_convex_jensen_scaled r m hr (by omega) hq hα hα1 hk
  have hp : (0 : ℝ) < r.choose m := by exact_mod_cast Nat.choose_pos (by omega : m ≤ r)
  have hl := bernsteinDeficitCoeff_lower s θ r m (by omega) hθ
    ((s.card.choose r : ℝ) - k * Ring.choose (q + α) r)
    (k * α * Ring.choose (q + 1) r) (k * (1 - α) * Ring.choose q r) ((q + 1) / q)
  rw [hmean] at hl
  have hpos := mul_pos hp (sub_pos.mpr hj)
  nlinarith only [hl, hpos]

theorem affine_power_expansion (r : ℕ) (L z : ℝ) :
    ((1 - z) + z * L) ^ r =
      ∑ m ∈ Finset.range (r + 1), (r.choose m : ℝ) * L ^ m * z ^ m * (1 - z) ^ (r - m) := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_pow]
  ring

theorem bernsteinDeficit_expansion (s : Finset V) (θ : V → ℝ) (r : ℕ)
    (C L U W ρ z : ℝ) :
    C * ((1 - z) + z * L) ^ r - esymmOn s r (fun v => (1 - z) + z * θ v) +
        U + W * ((1 - z) + z * ρ) ^ r =
      ∑ m ∈ Finset.range (r + 1),
        bernsteinDeficitCoeff s θ r m C L U W ρ * z ^ m * (1 - z) ^ (r - m) := by
  have hU : U = ∑ m ∈ Finset.range (r + 1),
      (r.choose m : ℝ) * U * z ^ m * (1 - z) ^ (r - m) := by
    calc
      U = U * ((1 - z) + z * 1) ^ r := by simp
      _ = _ := by
        rw [affine_power_expansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        simp only [one_pow]
        ring
  rw [affine_power_expansion, affine_power_expansion, esymmOn_affine]
  nth_rw 1 [hU]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  unfold bernsteinDeficitCoeff
  ring

theorem bernsteinDeficit_pos (s : Finset V) (θ : V → ℝ) (r : ℕ)
    (C L U W ρ : ℝ) (hcoeff : ∀ m ≤ r, 0 < bernsteinDeficitCoeff s θ r m C L U W ρ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < C * ((1 - z) + z * L) ^ r - esymmOn s r (fun v => (1 - z) + z * θ v) +
      U + W * ((1 - z) + z * ρ) ^ r := by
  rw [bernsteinDeficit_expansion]
  apply Finset.sum_pos'
  · intro m hm
    have hc := (hcoeff m (by have := Finset.mem_range.mp hm; omega)).le
    have hs : 0 ≤ 1 - z := sub_nonneg.mpr hz1
    positivity
  · by_cases hz : z < 1
    · refine ⟨0, by simp, ?_⟩
      simp only [pow_zero, mul_one, Nat.sub_zero]
      exact mul_pos (hcoeff 0 (Nat.zero_le _)) (pow_pos (sub_pos.mpr hz) r)
    · have hz : z = 1 := by linarith
      refine ⟨r, by simp, ?_⟩
      simpa only [hz, one_pow, mul_one, Nat.sub_self, pow_zero] using hcoeff r le_rfl

theorem esymmOn_scale (s : Finset V) (x : V → ℝ) (a : ℝ) (r : ℕ) :
    esymmOn s r (fun v => a * x v) = a ^ r * esymmOn s r x := by
  unfold esymmOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp he).2]

theorem sum_twoLevel_apply (s u : Finset V) (hu : u ⊆ s) (f : ℝ → ℝ) (a b : ℝ) :
    ∑ v ∈ s, f (twoLevelWeights u a b v) =
      (u.card : ℝ) * f a + ((s \ u).card : ℝ) * f b := by
  simp only [twoLevelWeights, apply_ite, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hu, Finset.filter_notMem_eq_sdiff]

theorem twoLevel_endpoint_moments (s u : Finset V) (hu : u ⊆ s)
    {q α k : ℝ} (hq : 0 < q) (hα : 0 < α) (hk : 0 < k)
    (hA : (u.card : ℝ) = k * α * (q + 1))
    (hB : ((s \ u).card : ℝ) = k * (1 - α) * q) :
    (s.card : ℝ) = k * (q + α) ∧
    (∑ v ∈ s, twoLevelWeights u 1 ((q + 1) / q) v) / s.card = (q + 1) / (q + α) ∧
    (∑ v ∈ s, twoLevelWeights u (1 / (q + 1)) (1 / q) v) =
      (s.card : ℝ) * (1 / (q + α)) ∧
    (∑ v ∈ s, (twoLevelWeights u (1 / (q + 1)) (1 / q) v - 1 / (q + α)) ^ 2) =
      k * α * (1 - α) / (q * (q + 1) * (q + α)) := by
  have hq1 : q + 1 ≠ 0 := ne_of_gt (by linarith : 0 < q + 1)
  have hν : q + α ≠ 0 := ne_of_gt (by positivity : 0 < q + α)
  have hc : (s.card : ℝ) = k * (q + α) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) (Finset.card_sdiff_add_card_eq_card hu)
    push_cast at h
    rw [hA, hB] at h
    nlinarith only [h]
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [sum_twoLevel_apply s u hu (fun z => z), hc, hA, hB]
    field_simp
    <;> ring
  · rw [sum_twoLevel_apply s u hu (fun z => z), hc, hA, hB]
    field_simp
    <;> ring
  · rw [sum_twoLevel_apply s u hu (fun z => (z - 1 / (q + α)) ^ 2), hA, hB]
    field_simp
    <;> ring

theorem bernsteinDeficitCoeff_pos_last_twoLevel (s u : Finset V) (hu : u ⊆ s)
    (r q : ℕ) (hr : 4 ≤ r) (hq : r - 1 ≤ q) (hn : 2 * q + 1 ≤ s.card)
    {α k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hk : 0 < k)
    (hA : (u.card : ℝ) = k * α * ((q : ℝ) + 1))
    (hB : ((s \ u).card : ℝ) = k * (1 - α) * q) :
    0 < bernsteinDeficitCoeff s (twoLevelWeights u 1 (((q : ℝ) + 1) / q)) r r
      ((s.card.choose r : ℝ) - k * Ring.choose ((q : ℝ) + α) r)
      (((q : ℝ) + 1) / ((q : ℝ) + α))
      (k * α * Ring.choose ((q : ℝ) + 1) r)
      (k * (1 - α) * Ring.choose (q : ℝ) r) (((q : ℝ) + 1) / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hν : (0 : ℝ) < (q : ℝ) + α := by positivity
  obtain ⟨hc, hmθ, hmw, hvw⟩ := twoLevel_endpoint_moments s u hu hq0 hα0 hk hA hB
  have hw : ∀ v ∈ s, 1 / ((q : ℝ) + 1) ≤ twoLevelWeights u
      (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)) v := by
    intro v hv
    unfold twoLevelWeights
    split_ifs
    · exact le_rfl
    · exact one_div_le_one_div_of_le hq0 (by linarith)
  have he := endpoint_esymm_strict s
    (twoLevelWeights u (1 / ((q : ℝ) + 1)) (1 / (q : ℝ))) r q hr hq hn
    hα0 hα1 hk hw hmw hvw
  have hscale : (fun v => ((q : ℝ) + 1) *
      twoLevelWeights u (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)) v) =
      twoLevelWeights u 1 (((q : ℝ) + 1) / q) := by
    funext v
    unfold twoLevelWeights
    split_ifs <;> field_simp
  have he' := mul_lt_mul_of_pos_left he (pow_pos hq1 r)
  rw [← esymmOn_scale, hscale] at he'
  simp only [bernsteinDeficitCoeff, Nat.choose_self, Nat.sub_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  have heq : ((q : ℝ) + 1) ^ r *
      ((s.card.choose r : ℝ) / ((q : ℝ) + α) ^ r -
        k * normalizedChoose r ((q : ℝ) + α) +
        k * (1 - α) * normalizedChoose r q + k * α * normalizedChoose r ((q : ℝ) + 1)) =
      ((s.card.choose r : ℝ) - k * Ring.choose ((q : ℝ) + α) r) *
        (((q : ℝ) + 1) / ((q : ℝ) + α)) ^ r + k * α * Ring.choose ((q : ℝ) + 1) r +
        k * (1 - α) * Ring.choose (q : ℝ) r * (((q : ℝ) + 1) / q) ^ r := by
    unfold normalizedChoose
    rw [div_pow, div_pow]
    field_simp
    <;> ring
  rw [heq] at he'
  linarith

/-- Strict positivity of the whole Bernstein expansion on the closed interval. -/
theorem balanced_affine_deficit_pos (s u : Finset V) (hu : u ⊆ s)
    (r q : ℕ) (hr : 4 ≤ r) (hq : r - 1 ≤ q) (hn : 2 * q + 1 ≤ s.card)
    {α k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hk : 0 < k)
    (hA : (u.card : ℝ) = k * α * ((q : ℝ) + 1))
    (hB : ((s \ u).card : ℝ) = k * (1 - α) * q)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < ((s.card.choose r : ℝ) - k * Ring.choose ((q : ℝ) + α) r) *
        ((1 - z) + z * (((q : ℝ) + 1) / ((q : ℝ) + α))) ^ r -
      esymmOn s r (fun v => (1 - z) + z * twoLevelWeights u 1 (((q : ℝ) + 1) / q) v) +
      k * α * Ring.choose ((q : ℝ) + 1) r +
      k * (1 - α) * Ring.choose (q : ℝ) r * ((1 - z) + z * (((q : ℝ) + 1) / q)) ^ r := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨hc, hmθ, hmw, hvw⟩ := twoLevel_endpoint_moments s u hu hq0 hα0 hk hA hB
  apply bernsteinDeficit_pos s _ r _ _ _ _ _ ?_ hz0 hz1
  intro m hm
  by_cases hmr : m = r
  · subst m
    exact bernsteinDeficitCoeff_pos_last_twoLevel s u hu r q hr hq hn hα0 hα1 hk hA hB
  · apply bernsteinDeficitCoeff_pos_before_last s _ r m (by omega) (by omega)
    · intro v hv
      unfold twoLevelWeights
      split_ifs <;> positivity
    · have h : (r : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast (show r ≤ q + 1 by omega)
      linarith
    · exact hα0
    · exact hα1
    · exact hk
    · exact hmθ

theorem twoLevel_explicit_strict_bound_real (s u : Finset V) (hu : u ⊆ s)
    (r q : ℕ) (hr : 4 ≤ r) (hq : r - 1 ≤ q) (hn : 2 * q + 1 ≤ s.card)
    {α k a b : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hk : 0 < k)
    (hA : (u.card : ℝ) = k * α * ((q : ℝ) + 1))
    (hB : ((s \ u).card : ℝ) = k * (1 - α) * q)
    (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ (((q : ℝ) + 1) / q) * a)
    (hsum : ∑ v ∈ s, twoLevelWeights u a b v = 1) :
    esymmOn s r (twoLevelWeights u a b) -
        k * α * Ring.choose ((q : ℝ) + 1) r * a ^ r -
        k * (1 - α) * Ring.choose (q : ℝ) r * b ^ r <
      ((s.card.choose r : ℝ) - k * Ring.choose ((q : ℝ) + α) r) / (s.card : ℝ) ^ r := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN : (0 : ℝ) < s.card := by exact_mod_cast (show 0 < s.card by omega)
  let z : ℝ := (q : ℝ) * (b / a - 1)
  let θ : V → ℝ := twoLevelWeights u 1 (((q : ℝ) + 1) / q)
  let L : ℝ := ((q : ℝ) + 1) / ((q : ℝ) + α)
  let ρ : ℝ := ((q : ℝ) + 1) / q
  let C : ℝ := (s.card.choose r : ℝ) - k * Ring.choose ((q : ℝ) + α) r
  let U : ℝ := k * α * Ring.choose ((q : ℝ) + 1) r
  let W : ℝ := k * (1 - α) * Ring.choose (q : ℝ) r
  have hz0 : 0 ≤ z := by
    apply mul_nonneg hq0.le
    exact sub_nonneg.mpr ((le_div_iff₀ ha).2 (by simpa using hab))
  have hz1 : z ≤ 1 := by
    have hb : b / a ≤ ((q : ℝ) + 1) / q := (div_le_iff₀ ha).2 hba
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hb 1) hq0.le
    have he : (q : ℝ) * ((((q : ℝ) + 1) / q) - 1) = 1 := by field_simp; ring
    rw [he] at h
    exact h
  have hb : a * ((1 - z) + z * ρ) = b := by
    dsimp [z, ρ]
    field_simp
    <;> ring
  have hvec : twoLevelWeights u a b = fun v => a * ((1 - z) + z * θ v) := by
    funext v
    dsimp [θ, twoLevelWeights]
    split_ifs
    · ring
    · exact hb.symm
  obtain ⟨hc, hmθ, hmw, hvw⟩ := twoLevel_endpoint_moments s u hu hq0 hα0 hk hA hB
  have hθsum : ∑ v ∈ s, θ v = (s.card : ℝ) * L := by
    have h := (div_eq_iff hN.ne').mp hmθ
    dsimp [θ, L]
    nlinarith only [h]
  have hsum' : a * ((s.card : ℝ) * (1 - z) + z * ∑ v ∈ s, θ v) = 1 := by
    rw [hvec, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum] at hsum
    exact hsum
  rw [hθsum] at hsum'
  have hunit : a * ((1 - z) + z * L) = 1 / (s.card : ℝ) := by
    apply (eq_div_iff hN.ne').2
    nlinarith only [hsum']
  have hunitpow : a ^ r * ((1 - z) + z * L) ^ r = 1 / (s.card : ℝ) ^ r := by
    rw [← mul_pow, hunit, one_div_pow]
  have hbpow : a ^ r * ((1 - z) + z * ρ) ^ r = b ^ r := by rw [← mul_pow, hb]
  have hp : 0 < C * ((1 - z) + z * L) ^ r -
      esymmOn s r (fun v => (1 - z) + z * θ v) + U + W * ((1 - z) + z * ρ) ^ r :=
    balanced_affine_deficit_pos s u hu r q hr hq hn hα0 hα1 hk hA hB hz0 hz1
  have hscaled := mul_pos (pow_pos ha r) hp
  have he : a ^ r * (C * ((1 - z) + z * L) ^ r -
      esymmOn s r (fun v => (1 - z) + z * θ v) + U + W * ((1 - z) + z * ρ) ^ r) =
      C / (s.card : ℝ) ^ r - (esymmOn s r (twoLevelWeights u a b) - U * a ^ r - W * b ^ r) := by
    rw [hvec, esymmOn_scale]
    calc
      _ = C * (a ^ r * ((1 - z) + z * L) ^ r) -
          a ^ r * esymmOn s r (fun v => (1 - z) + z * θ v) + U * a ^ r +
          W * (a ^ r * ((1 - z) + z * ρ) ^ r) := by ring
      _ = _ := by rw [hunitpow, hbpow]; ring
  rw [he] at hscaled
  exact sub_pos.mp hscaled

/-- The explicit Lagrangian estimate on the ratio interval of Claim 6.3.
All parameters here are the integer class parameters of a balanced colouring. -/
theorem twoLevel_explicit_strict_bound (s u : Finset V) (hu : u ⊆ s)
    (r k q t : ℕ) (hr : 4 ≤ r) (hk : 2 ≤ k) (hq : r - 1 ≤ q)
    (ht : 0 < t) (htk : t < k)
    (hA : u.card = t * (q + 1)) (hB : (s \ u).card = (k - t) * q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ (((q : ℝ) + 1) / q) * a)
    (hsum : ∑ v ∈ s, twoLevelWeights u a b v = 1) :
    esymmOn s r (twoLevelWeights u a b) -
        (t : ℝ) * ((q + 1).choose r : ℝ) * a ^ r -
        ((k - t : ℕ) : ℝ) * (q.choose r : ℝ) * b ^ r <
      ((s.card.choose r : ℝ) - (k : ℝ) * Ring.choose ((s.card : ℝ) / k) r) /
        (s.card : ℝ) ^ r := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hα0 : (0 : ℝ) < (t : ℝ) / k := div_pos ht0 hk0
  have hα1 : (t : ℝ) / k < 1 := (div_lt_one hk0).2 (by exact_mod_cast htk)
  have hA' : (u.card : ℝ) = (k : ℝ) * ((t : ℝ) / k) * ((q : ℝ) + 1) := by
    rw [hA]
    push_cast
    field_simp
  have hB' : ((s \ u).card : ℝ) = (k : ℝ) * (1 - (t : ℝ) / k) * q := by
    rw [hB]
    push_cast [Nat.cast_sub htk.le]
    field_simp
    <;> ring
  have hc : s.card = k * q + t := by
    have h := Finset.card_sdiff_add_card_eq_card hu
    rw [hA, hB] at h
    have he : (k - t) * q + t * q = k * q := by
      rw [← Nat.add_mul, Nat.sub_add_cancel htk.le]
    nlinarith only [h, he]
  have hn : 2 * q + 1 ≤ s.card := by
    rw [hc]
    nlinarith [Nat.mul_le_mul_right q hk]
  have h := twoLevel_explicit_strict_bound_real s u hu r q hr hq hn hα0 hα1 hk0
    hA' hB' ha hab hba hsum
  have hν : (q : ℝ) + (t : ℝ) / k = (s.card : ℝ) / k := by
    rw [hc]
    push_cast
    field_simp
  have hbig : Ring.choose ((q : ℝ) + 1) r = ((q + 1).choose r : ℝ) := by
    rw [show (q : ℝ) + 1 = ((q + 1 : ℕ) : ℝ) by push_cast; rfl, realChoose_natCast]
  have hkt : (k : ℝ) * (1 - (t : ℝ) / k) = ((k - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub htk.le]
    field_simp
  have ht' : (k : ℝ) * ((t : ℝ) / k) = t := by field_simp
  rw [hν, hbig, realChoose_natCast, hkt, ht'] at h
  exact h

end ChromaticSpectral
