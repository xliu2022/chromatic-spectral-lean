module

public import ChromaticSpectral.Basic

/-! # Variational spectral radius on finite vertex types
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

theorem PWeights.apply_rpow_le_one {p : ℝ} {x : V → ℝ}
    (hx : PWeights p x) (v : V) : (x v) ^ p ≤ 1 := by
  calc
    (x v) ^ p ≤ ∑ w, (x w) ^ p :=
      Finset.single_le_sum (fun w _ => Real.rpow_nonneg (hx.1 w) _) (Finset.mem_univ v)
    _ = 1 := hx.2

theorem PWeights.apply_le_one {p : ℝ} (hp : 0 < p) {x : V → ℝ}
    (hx : PWeights p x) (v : V) : x v ≤ 1 := by
  by_contra h
  exact (not_lt_of_ge (hx.apply_rpow_le_one v)) (Real.one_lt_rpow (lt_of_not_ge h) hp)

theorem pWeights_isCompact {p : ℝ} (hp : 0 < p) :
    IsCompact {x : V → ℝ | PWeights p x} := by
  have hclosed : IsClosed {x : V → ℝ | PWeights p x} := by
    have hi : IsClosed (⋂ v : V, {x : V → ℝ | 0 ≤ x v}) :=
      isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
    have hc : Continuous (fun x : V → ℝ => ∑ v, (x v) ^ p) := by
      apply continuous_finsetSum
      intro v _
      exact (Real.continuous_rpow_const hp.le).comp (continuous_apply v)
    have he : IsClosed {x : V → ℝ | ∑ v, (x v) ^ p = 1} :=
      isClosed_eq hc continuous_const
    convert hi.inter he using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, PWeights]
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (0 : V → ℝ)) (b := 1)) hclosed
  intro x hx
  exact ⟨hx.1, fun v => hx.apply_le_one hp v⟩

theorem pWeights_nonempty [Nonempty V] {p : ℝ} (hp : 0 < p) :
    ({x : V → ℝ | PWeights p x} : Set (V → ℝ)).Nonempty := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨fun w => if w = v then 1 else 0, ?_, ?_⟩
  · intro w
    dsimp only
    split_ifs <;> positivity
  · simp [hp.ne']

namespace RGraph
variable {r : ℕ}

theorem edgePolynomial_nonneg (G : RGraph V r) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) : 0 ≤ G.edgePolynomial x := by
  exact Finset.sum_nonneg (fun e _ => Finset.prod_nonneg (fun v _ => hx v))

theorem polyform_nonneg (G : RGraph V r) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) : 0 ≤ G.polyform x :=
  mul_nonneg (Nat.cast_nonneg _) (G.edgePolynomial_nonneg hx)

theorem continuous_polyform (G : RGraph V r) : Continuous G.polyform := by
  unfold polyform edgePolynomial
  fun_prop

theorem edgePolynomial_mono {G H : RGraph V r} (h : G.IsSubgraph H)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) : G.edgePolynomial x ≤ H.edgePolynomial x :=
  Finset.sum_le_sum_of_subset_of_nonneg h
    (fun e _ _ => Finset.prod_nonneg (fun v _ => hx v))

theorem polyform_mono {G H : RGraph V r} (h : G.IsSubgraph H)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) : G.polyform x ≤ H.polyform x :=
  mul_le_mul_of_nonneg_left (edgePolynomial_mono h hx) (Nat.cast_nonneg _)

theorem edgePolynomial_const (G : RGraph V r) (c : ℝ) :
    G.edgePolynomial (fun _ => c) = (G.edges.card : ℝ) * c ^ r := by
  unfold edgePolynomial
  simp only [Finset.prod_const]
  calc
    (∑ e ∈ G.edges, c ^ e.card) = ∑ _e ∈ G.edges, c ^ r :=
      Finset.sum_congr rfl (fun e he => by rw [G.uniform e he])
    _ = _ := by simp

theorem edgePolynomial_smul (G : RGraph V r) (c : ℝ) (x : V → ℝ) :
    G.edgePolynomial (fun v => c * x v) = c ^ r * G.edgePolynomial x := by
  simp only [edgePolynomial, Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e he => by rw [G.uniform e he])

theorem polyform_smul (G : RGraph V r) (c : ℝ) (x : V → ℝ) :
    G.polyform (fun v => c * x v) = c ^ r * G.polyform x := by
  rw [polyform, edgePolynomial_smul, polyform]
  ring

theorem polyform_le_abs (G : RGraph V r) (x : V → ℝ) :
    G.polyform x ≤ G.polyform (fun v => |x v|) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r.factorial)
  apply Finset.sum_le_sum
  intro e _
  calc
    (∏ v ∈ e, x v) ≤ |∏ v ∈ e, x v| := le_abs_self _
    _ = ∏ v ∈ e, |x v| := Finset.abs_prod _ _

theorem spectralValues_nonempty (G : RGraph V r) (p : ℝ) :
    (G.spectralValues p).Nonempty := ⟨0, Set.mem_insert _ _⟩

theorem spectralValues_bddAbove (G : RGraph V r) {p : ℝ} (hp : 0 < p) :
    BddAbove (G.spectralValues p) := by
  refine ⟨(r.factorial : ℝ) * G.edges.card, ?_⟩
  intro z hz
  rcases hz with rfl | ⟨x, hx, rfl⟩
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      G.edgePolynomial x ≤ ∑ _e ∈ G.edges, (1 : ℝ) :=
        Finset.sum_le_sum fun e _ =>
          Finset.prod_le_one₀ (fun v _ => hx.1 v) (fun v _ => hx.apply_le_one hp v)
      _ = _ := by simp

theorem pSpectralRadius_nonneg (G : RGraph V r) {p : ℝ} (hp : 0 < p) :
    0 ≤ G.pSpectralRadius p :=
  le_csSup (G.spectralValues_bddAbove hp) (Set.mem_insert _ _)

theorem polyform_le_pSpectralRadius (G : RGraph V r) {p : ℝ} (hp : 0 < p)
    {x : V → ℝ} (hx : PWeights p x) : G.polyform x ≤ G.pSpectralRadius p :=
  le_csSup (G.spectralValues_bddAbove hp) (Or.inr ⟨x, hx, rfl⟩)

theorem pSpectralRadius_le_iff (G : RGraph V r) {p b : ℝ} (hp : 0 < p)
    (hb : 0 ≤ b) : G.pSpectralRadius p ≤ b ↔
      ∀ x : V → ℝ, PWeights p x → G.polyform x ≤ b := by
  constructor
  · intro h x hx
    exact (G.polyform_le_pSpectralRadius hp hx).trans h
  · intro h
    apply csSup_le (G.spectralValues_nonempty p)
    intro z hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact hb
    · exact h x hx

theorem exists_maximizer [Nonempty V] (G : RGraph V r) {p : ℝ} (hp : 0 < p) :
    ∃ x : V → ℝ, G.IsMaximizer p x := by
  obtain ⟨x, hx, hmax⟩ := (pWeights_isCompact hp).exists_isMaxOn
    (pWeights_nonempty hp) G.continuous_polyform.continuousOn
  refine ⟨x, hx, le_antisymm (G.polyform_le_pSpectralRadius hp hx) ?_⟩
  apply (G.pSpectralRadius_le_iff hp (G.polyform_nonneg hx.1)).mpr
  exact fun y hy => hmax hy

theorem pSpectralRadius_mono {G H : RGraph V r} {p : ℝ} (hp : 0 < p)
    (h : G.IsSubgraph H) : G.pSpectralRadius p ≤ H.pSpectralRadius p := by
  apply (G.pSpectralRadius_le_iff hp (H.pSpectralRadius_nonneg hp)).mpr
  intro x hx
  exact (polyform_mono h hx.1).trans (H.polyform_le_pSpectralRadius hp hx)

/-- The variational definition agrees with optimization over arbitrary signed
real vectors: absolute values do not decrease the edge polynomial. -/
theorem signed_polyform_le_pSpectralRadius (G : RGraph V r) {p : ℝ}
    (hp : 0 < p) (x : V → ℝ) (hx : ∑ v, |x v| ^ p = 1) :
    G.polyform x ≤ G.pSpectralRadius p :=
  (G.polyform_le_abs x).trans (G.polyform_le_pSpectralRadius hp ⟨fun _ => abs_nonneg _, hx⟩)

end RGraph
end ChromaticSpectral
