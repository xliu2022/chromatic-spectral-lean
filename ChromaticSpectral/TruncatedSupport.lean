module

public import ChromaticSpectral.TruncatedMoments

/-! # Reducing truncated-moment comparison to finitely many support points -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

theorem truncatedMoment_mono {I : Type} (S : Finset I) (a x : I → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) : Monotone (truncatedMoment S a x) := by
  intro T V hTV
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (min_le_min_right _ hTV) (ha i hi)

theorem truncatedMoment_concave {I : Type} (S : Finset I) (a x : I → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) : ConcaveOn ℝ Set.univ (truncatedMoment S a x) := by
  refine ⟨convex_univ, ?_⟩
  intro T hT V hV q r hq hr hqr
  simp only [truncatedMoment, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h₁ : q * min T (x i) + r * min V (x i) ≤ q * T + r * V :=
    add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hq)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hr)
  have h₂ : q * min T (x i) + r * min V (x i) ≤ x i := by
    calc
      _ ≤ q * x i + r * x i :=
        add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) hq)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hr)
      _ = x i := by rw [← add_mul, hqr, one_mul]
  have h := mul_le_mul_of_nonneg_left (le_min h₁ h₂) (ha i hi)
  nlinarith

theorem truncatedMoment_difference_concaveOn {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) {l r : ℝ}
    (hgap : ∀ j ∈ U, y j ≤ l ∨ r ≤ y j) :
    ConcaveOn ℝ (Set.Icc l r)
      (fun T => truncatedMoment S a x T - truncatedMoment U b y T) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro T hT V hV q d hq hd hqd
  have hmix : q * T + d * V ∈ Set.Icc l r := by
    simpa only [smul_eq_mul] using (convex_Icc l r) hT hV hq hd hqd
  have hlinear : truncatedMoment U b y (q * T + d * V) =
      q * truncatedMoment U b y T + d * truncatedMoment U b y V := by
    simp only [truncatedMoment, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases hgap j hj with hj | hj
    · rw [min_eq_right (hj.trans hmix.1), min_eq_right (hj.trans hT.1),
        min_eq_right (hj.trans hV.1)]
      nlinarith [congrArg (fun z : ℝ => z * (b j * y j)) hqd]
    · rw [min_eq_left (hmix.2.trans hj), min_eq_left (hT.2.trans hj),
        min_eq_left (hV.2.trans hj)]
      ring
  have h := (truncatedMoment_concave S a x ha).2 (Set.mem_univ T) (Set.mem_univ V)
    hq hd hqd
  simp only [smul_eq_mul] at h ⊢
  rw [hlinear]
  linarith

theorem truncatedMoment_le_of_support_checks {I J : Type}
    (S : Finset I) (U : Finset J) (a x : I → ℝ) (b y : J → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ j ∈ U, 0 ≤ y j)
    (hchecks : ∀ j ∈ U, truncatedMoment U b y (y j) ≤
      truncatedMoment S a x (y j)) :
    ∀ T, 0 ≤ T → truncatedMoment U b y T ≤ truncatedMoment S a x T := by
  classical
  let K := insert (0 : ℝ) (U.image y)
  have hK0 : (0 : ℝ) ∈ K := Finset.mem_insert_self _ _
  have hKne : K.Nonempty := ⟨0, hK0⟩
  let H : ℝ → ℝ := fun T => truncatedMoment S a x T - truncatedMoment U b y T
  have hH0 : H 0 = 0 := by
    have hS : truncatedMoment S a x 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [min_eq_left (hx i hi), mul_zero]
    have hU : truncatedMoment U b y 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [min_eq_left (hy i hi), mul_zero]
    simp [H, hS, hU]
  have hHK : ∀ z ∈ K, 0 ≤ H z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp [hH0]
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact sub_nonneg.mpr (hchecks j hj)
  intro T hT
  apply sub_nonneg.mp
  change 0 ≤ H T
  by_cases hmax : ∀ z ∈ K, z ≤ T
  · let M := K.max' hKne
    have hM : M ∈ K := Finset.max'_mem K hKne
    have hMT : M ≤ T := hmax M hM
    have hmaxy : ∀ j ∈ U, y j ≤ M := by
      intro j hj
      exact Finset.le_max' K (y j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    have hconst : truncatedMoment U b y T = truncatedMoment U b y M := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [min_eq_right ((hmaxy j hj).trans hMT), min_eq_right (hmaxy j hj)]
    have hmono := truncatedMoment_mono S a x ha hMT
    have hHM := hHK M hM
    dsimp [H] at *
    rw [hconst]
    linarith
  · push Not at hmax
    obtain ⟨z, hz, hTz⟩ := hmax
    let L := K.filter (fun z => z ≤ T)
    let R := K.filter (fun z => T ≤ z)
    have hLne : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hK0, hT⟩⟩
    have hRne : R.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨hz, hTz.le⟩⟩
    let l := L.max' hLne
    let r := R.min' hRne
    have hlL : l ∈ L := Finset.max'_mem L hLne
    have hrR : r ∈ R := Finset.min'_mem R hRne
    have hlK : l ∈ K := (Finset.mem_filter.mp hlL).1
    have hrK : r ∈ K := (Finset.mem_filter.mp hrR).1
    have hlT : l ≤ T := (Finset.mem_filter.mp hlL).2
    have hTr : T ≤ r := (Finset.mem_filter.mp hrR).2
    have hgap : ∀ j ∈ U, y j ≤ l ∨ r ≤ y j := by
      intro j hj
      have hjK : y j ∈ K := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
      by_cases hjT : y j ≤ T
      · exact Or.inl (Finset.le_max' L (y j) (Finset.mem_filter.mpr ⟨hjK, hjT⟩))
      · exact Or.inr (Finset.min'_le R (y j)
          (Finset.mem_filter.mpr ⟨hjK, (lt_of_not_ge hjT).le⟩))
    have hc := truncatedMoment_difference_concaveOn S U a x b y ha hgap
    have hlr : l ≤ r := hlT.trans hTr
    exact (le_min (hHK l hlK) (hHK r hrK)).trans
      (hc.min_le_of_mem_Icc ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩ ⟨hlT, hTr⟩)

end ChromaticSpectral
