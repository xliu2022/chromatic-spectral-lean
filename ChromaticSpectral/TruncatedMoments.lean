module

public import ChromaticSpectral.Basic

/-!
# Truncated moments and finite concave interpolation

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.

The proof uses only finitely many interpolation knots. No improper
integrals or measures are needed for the finite-support inequalities.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

def truncatedMoment {I : Type*} (S : Finset I) (w x : I → ℝ) (T : ℝ) : ℝ :=
  ∑ i ∈ S, w i * min T (x i)

theorem finite_summation_by_parts (d w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (d i - d (i + 1)) * w (i + 1)) =
      d 0 * w 0 - d n * w n +
        ∑ i ∈ Finset.range n, d i * (w (i + 1) - w i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, ih]
    ring

noncomputable def knotSlope (f : ℝ → ℝ) (t : ℕ → ℝ) (n i : ℕ) : ℝ :=
  if i < n then (f (t (i + 1)) - f (t i)) / (t (i + 1) - t i) else 0

theorem min_interpolation_at_knot (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht0 : t 0 = 0) (hf0 : f 0 = 0)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    {k : ℕ} (hk : k ≤ n) :
    (∑ i ∈ Finset.range n,
      (knotSlope f t n i - knotSlope f t n (i + 1)) * min (t (i + 1)) (t k)) =
      f (t k) := by
  have htmono : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
    intro i j hij hj
    rcases hij.eq_or_lt with h | h
    · simp [h]
    · exact (ht i j h hj).le
  have htk : 0 ≤ t k := by simpa [ht0] using htmono 0 k (Nat.zero_le _) hk
  rw [finite_summation_by_parts (knotSlope f t n) (fun i => min (t i) (t k)) n]
  simp only [ht0, min_eq_left htk, mul_zero, knotSlope, lt_self_iff_false,
    ↓reduceIte, zero_mul, sub_self, zero_add]
  have hre :
      (∑ i ∈ Finset.range n,
        (if i < n then (f (t (i + 1)) - f (t i)) / (t (i + 1) - t i) else 0) *
          (min (t (i + 1)) (t k) - min (t i) (t k))) =
      ∑ i ∈ Finset.range k, (f (t (i + 1)) - f (t i)) := by
    calc
      _ = ∑ i ∈ Finset.range k,
          (if i < n then (f (t (i + 1)) - f (t i)) / (t (i + 1) - t i) else 0) *
            (min (t (i + 1)) (t k) - min (t i) (t k)) := by
        apply (Finset.sum_subset (Finset.range_mono hk) ?_).symm
        intro i hi hik
        have hik' : k ≤ i := Nat.le_of_not_gt (by simpa using hik)
        have hin : i < n := Finset.mem_range.mp hi
        rw [min_eq_right (htmono k (i + 1) (by omega) (by omega)),
          min_eq_right (htmono k i hik' (by omega)), sub_self, mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hin : i < n := lt_of_lt_of_le hik hk
        rw [ite_eq_left hin, min_eq_left (htmono (i + 1) k (by omega) hk),
          min_eq_left (htmono i k (by omega) hk)]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr (ht i (i + 1) (by omega) (by omega)).ne')
  rw [hre, Finset.sum_range_sub (fun i => f (t i)) k]
  simp [ht0, hf0]

theorem knotSlope_nonneg (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    (hf : ∀ i j, i ≤ j → j ≤ n → f (t i) ≤ f (t j)) (i : ℕ) :
    0 ≤ knotSlope f t n i := by
  unfold knotSlope
  split_ifs with hi
  · exact div_nonneg (sub_nonneg.mpr (hf i (i + 1) (by omega) (by omega)))
      (sub_nonneg.mpr (ht i (i + 1) (by omega) (by omega)).le)
  · exact le_rfl

theorem knotSlope_antitone (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht0 : t 0 = 0)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    (hf : MonotoneOn f (Set.Ici 0)) (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (i : ℕ) : knotSlope f t n (i + 1) ≤ knotSlope f t n i := by
  have ht_nonneg : ∀ j, j ≤ n → 0 ≤ t j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [ht0]
    · simpa [ht0] using (ht 0 j hj0 hj).le
  by_cases hi : i + 1 < n
  · simp only [knotSlope, ite_eq_left hi, ite_eq_left (show i < n by omega)]
    exact hconc.slope_anti_adjacent (ht_nonneg i (by omega))
      (ht_nonneg (i + 1 + 1) (by omega))
      (ht i (i + 1) (by omega) (by omega))
      (ht (i + 1) (i + 1 + 1) (by omega) (by omega))
  · rw [knotSlope, ite_eq_right hi]
    apply knotSlope_nonneg f t n ht
    intro a b hab hbn
    apply hf (ht_nonneg a (by omega)) (ht_nonneg b hbn)
    rcases hab.eq_or_lt with h | h
    · simp [h]
    · exact (ht a b h hbn).le

theorem truncatedMoment_interpolation {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht0 : t 0 = 0) (hf0 : f 0 = 0)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    (hx : ∀ i ∈ S, ∃ j ≤ n, x i = t j)
    (hy : ∀ i ∈ U, ∃ j ≤ n, y i = t j) :
    (∑ i ∈ S, a i * f (x i)) - (∑ i ∈ U, b i * f (y i)) =
      ∑ j ∈ Finset.range n,
        (knotSlope f t n j - knotSlope f t n (j + 1)) *
          (truncatedMoment S a x (t (j + 1)) -
            truncatedMoment U b y (t (j + 1))) := by
  have hrepr : ∀ {z}, (∃ j ≤ n, z = t j) → f z =
      ∑ j ∈ Finset.range n,
        (knotSlope f t n j - knotSlope f t n (j + 1)) * min (t (j + 1)) z := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := hz
    exact (min_interpolation_at_knot f t n ht0 hf0 ht hj).symm
  have hsum : ∀ {K : Type} (V : Finset K) (w z : K → ℝ),
      (∀ i ∈ V, ∃ j ≤ n, z i = t j) →
      (∑ i ∈ V, w i * f (z i)) =
        ∑ j ∈ Finset.range n,
          (knotSlope f t n j - knotSlope f t n (j + 1)) *
            truncatedMoment V w z (t (j + 1)) := by
    intro K V w z hz
    calc
      _ = ∑ i ∈ V, w i *
          ∑ j ∈ Finset.range n,
            (knotSlope f t n j - knotSlope f t n (j + 1)) *
              min (t (j + 1)) (z i) := by
        exact Finset.sum_congr rfl fun i hi => congrArg (w i * ·) (hrepr (hz i hi))
      _ = _ := by
        simp only [Finset.mul_sum, truncatedMoment]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hsum S a x hx, hsum U b y hy, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem concave_sum_le_of_truncatedMoment_le_at_knots {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht0 : t 0 = 0) (hf0 : f 0 = 0)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    (hx : ∀ i ∈ S, ∃ j ≤ n, x i = t j)
    (hy : ∀ i ∈ U, ∃ j ≤ n, y i = t j)
    (hf : MonotoneOn f (Set.Ici 0)) (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hmom : ∀ j < n, truncatedMoment U b y (t (j + 1)) ≤
      truncatedMoment S a x (t (j + 1))) :
    (∑ i ∈ U, b i * f (y i)) ≤ ∑ i ∈ S, a i * f (x i) := by
  apply sub_nonneg.mp
  rw [truncatedMoment_interpolation S U a x b y f t n ht0 hf0 ht hx hy]
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (sub_nonneg.mpr (knotSlope_antitone f t n ht0 ht hf hconc j))
    (sub_nonneg.mpr (hmom j (Finset.mem_range.mp hj)))

theorem exists_ordered_knots (K : Finset ℝ) (h0 : (0 : ℝ) ∈ K)
    (hK : ∀ z ∈ K, 0 ≤ z) :
    ∃ n : ℕ, ∃ t : ℕ → ℝ, t 0 = 0 ∧
      (∀ i j, i < j → j ≤ n → t i < t j) ∧
      (∀ z ∈ K, ∃ j ≤ n, z = t j) := by
  classical
  have hcard : 0 < K.card := Finset.card_pos.mpr ⟨0, h0⟩
  let n := K.card - 1
  let t : ℕ → ℝ := fun i =>
    if hi : i < K.card then K.orderEmbOfFin rfl ⟨i, hi⟩ else 0
  refine ⟨n, t, ?_, ?_, ?_⟩
  · dsimp [t]
    rw [dite_eq_left hcard, Finset.orderEmbOfFin_zero rfl hcard]
    exact le_antisymm (Finset.min'_le K 0 h0)
      (hK _ (Finset.min'_mem K ⟨0, h0⟩))
  · intro i j hij hj
    have hjcard : j < K.card := by dsimp [n] at hj; omega
    have hicard : i < K.card := lt_trans hij hjcard
    dsimp [t]
    rw [dite_eq_left hicard, dite_eq_left hjcard]
    exact (K.orderEmbOfFin rfl).strictMono hij
  · intro z hz
    let j := (K.orderIsoOfFin rfl).symm ⟨z, hz⟩
    have hj : j.val ≤ n := by dsimp [n]; have := j.isLt; omega
    refine ⟨j.val, hj, ?_⟩
    dsimp [t]
    rw [ite_eq_left j.isLt]
    change z = ((K.orderIsoOfFin rfl) j).val
    simp [j]

theorem concave_sum_le_of_truncatedMoment_le {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ U, 0 ≤ y i)
    (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : MonotoneOn f (Set.Ici 0)) (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hmom : ∀ T, 0 ≤ T → truncatedMoment U b y T ≤ truncatedMoment S a x T) :
    (∑ i ∈ U, b i * f (y i)) ≤ ∑ i ∈ S, a i * f (x i) := by
  classical
  let K := insert (0 : ℝ) (S.image x ∪ U.image y)
  have h0 : (0 : ℝ) ∈ K := Finset.mem_insert_self _ _
  have hK : ∀ z ∈ K, 0 ≤ z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hx i hi
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hy i hi
  obtain ⟨n, t, ht0, ht, hsupport⟩ := exists_ordered_knots K h0 hK
  apply concave_sum_le_of_truncatedMoment_le_at_knots S U a x b y f t n ht0 hf0 ht
  · intro i hi
    exact hsupport _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  · intro i hi
    exact hsupport _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  · exact hf
  · exact hconc
  · intro j hj
    apply hmom
    have hpos := ht 0 (j + 1) (by omega) (by omega)
    simpa [ht0] using hpos.le

theorem rpow_sum_le_of_truncatedMoment_le {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ U, 0 ≤ y i)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmom : ∀ T, 0 ≤ T → truncatedMoment U b y T ≤ truncatedMoment S a x T) :
    (∑ i ∈ U, b i * (y i) ^ θ) ≤ ∑ i ∈ S, a i * (x i) ^ θ := by
  apply concave_sum_le_of_truncatedMoment_le S U a x b y hx hy (fun z => z ^ θ)
    (Real.zero_rpow hθ.ne')
  · intro u hu v hv huv
    exact Real.rpow_le_rpow hu huv hθ.le
  · exact Real.concaveOn_rpow hθ.le hθ1
  · exact hmom

theorem truncatedMoment_last_knot {I : Type} (S : Finset I) (a x : I → ℝ)
    (t : ℕ → ℝ) (n : ℕ)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    (hx : ∀ i ∈ S, ∃ j ≤ n, x i = t j) :
    truncatedMoment S a x (t n) = ∑ i ∈ S, a i * x i := by
  unfold truncatedMoment
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨j, hj, heq⟩ := hx i hi
  rw [heq, min_eq_right]
  rcases hj.eq_or_lt with rfl | hj
  · exact le_rfl
  · exact (ht j n hj le_rfl).le

theorem concave_sum_lt_of_truncatedMoment_le_at_knots {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht0 : t 0 = 0) (hf0 : f 0 = 0)
    (ht : ∀ i j, i < j → j ≤ n → t i < t j)
    (hx : ∀ i ∈ S, ∃ j ≤ n, x i = t j)
    (hy : ∀ i ∈ U, ∃ j ≤ n, y i = t j)
    (hf : StrictMonoOn f (Set.Ici 0)) (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hmom : ∀ j < n, truncatedMoment U b y (t (j + 1)) ≤
      truncatedMoment S a x (t (j + 1)))
    (htotal : (∑ i ∈ U, b i * y i) < ∑ i ∈ S, a i * x i) :
    (∑ i ∈ U, b i * f (y i)) < ∑ i ∈ S, a i * f (x i) := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hx0 : ∀ i ∈ S, x i = 0 := by
      intro i hi
      obtain ⟨j, hj, heq⟩ := hx i hi
      have : j = 0 := by omega
      simpa [this, ht0] using heq
    have hy0 : ∀ i ∈ U, y i = 0 := by
      intro i hi
      obtain ⟨j, hj, heq⟩ := hy i hi
      have : j = 0 := by omega
      simpa [this, ht0] using heq
    have hax : (∑ i ∈ S, a i * x i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hx0 i hi, mul_zero]
    have hby : (∑ i ∈ U, b i * y i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hy0 i hi, mul_zero]
    linarith
  have hnlast : n - 1 + 1 = n := by omega
  have ht_nonneg : ∀ j, j ≤ n → 0 ≤ t j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [ht0]
    · simpa [ht0] using (ht 0 j hj0 hj).le
  have hlastslope : 0 < knotSlope f t n (n - 1) - knotSlope f t n n := by
    have hstep := ht (n - 1) n (by omega) le_rfl
    simp only [knotSlope, ite_eq_left (show n - 1 < n by omega),
      ite_eq_right (show ¬ n < n from lt_irrefl n), hnlast, sub_zero]
    exact div_pos (sub_pos.mpr (hf (ht_nonneg _ (by omega))
      (ht_nonneg _ le_rfl) hstep)) (sub_pos.mpr hstep)
  apply sub_pos.mp
  rw [truncatedMoment_interpolation S U a x b y f t n ht0 hf0 ht hx hy]
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg
      (sub_nonneg.mpr (knotSlope_antitone f t n ht0 ht hf.monotoneOn hconc j))
      (sub_nonneg.mpr (hmom j (Finset.mem_range.mp hj)))
  · refine ⟨n - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [hnlast]
    apply mul_pos hlastslope
    rw [truncatedMoment_last_knot S a x t n ht hx,
      truncatedMoment_last_knot U b y t n ht hy]
    exact sub_pos.mpr htotal

theorem concave_sum_lt_of_truncatedMoment_le {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ U, 0 ≤ y i)
    (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : StrictMonoOn f (Set.Ici 0)) (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hmom : ∀ T, 0 ≤ T → truncatedMoment U b y T ≤ truncatedMoment S a x T)
    (htotal : (∑ i ∈ U, b i * y i) < ∑ i ∈ S, a i * x i) :
    (∑ i ∈ U, b i * f (y i)) < ∑ i ∈ S, a i * f (x i) := by
  classical
  let K := insert (0 : ℝ) (S.image x ∪ U.image y)
  have h0 : (0 : ℝ) ∈ K := Finset.mem_insert_self _ _
  have hK : ∀ z ∈ K, 0 ≤ z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hx i hi
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hy i hi
  obtain ⟨n, t, ht0, ht, hsupport⟩ := exists_ordered_knots K h0 hK
  apply concave_sum_lt_of_truncatedMoment_le_at_knots S U a x b y f t n ht0 hf0 ht
  · intro i hi
    exact hsupport _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  · intro i hi
    exact hsupport _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  · exact hf
  · exact hconc
  · intro j hj
    apply hmom
    have hpos := ht 0 (j + 1) (by omega) (by omega)
    simpa [ht0] using hpos.le
  · exact htotal

theorem rpow_sum_lt_of_truncatedMoment_le {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ U, 0 ≤ y i)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmom : ∀ T, 0 ≤ T → truncatedMoment U b y T ≤ truncatedMoment S a x T)
    (htotal : (∑ i ∈ U, b i * y i) < ∑ i ∈ S, a i * x i) :
    (∑ i ∈ U, b i * (y i) ^ θ) < ∑ i ∈ S, a i * (x i) ^ θ := by
  apply concave_sum_lt_of_truncatedMoment_le S U a x b y hx hy (fun z => z ^ θ)
    (Real.zero_rpow hθ.ne')
  · intro u hu v hv huv
    exact Real.rpow_lt_rpow hu huv hθ
  · exact Real.concaveOn_rpow hθ.le hθ1
  · exact hmom
  · exact htotal

end ChromaticSpectral
