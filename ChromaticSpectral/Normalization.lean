module

public import ChromaticSpectral.SpectralBasic

/-! # Homogeneous normalization and the nonnegative p-ball
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

theorem PWeights.normalize {p : ℝ} (hp : 0 < p) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hS : 0 < ∑ v, (x v) ^ p) :
    PWeights p (fun v => (∑ w, (x w) ^ p) ^ (-1 / p) * x v) := by
  constructor
  · intro v
    exact mul_nonneg (Real.rpow_nonneg hS.le _) (hx v)
  · calc
      (∑ v, ((∑ w, (x w) ^ p) ^ (-1 / p) * x v) ^ p) =
          ∑ v, ((∑ w, (x w) ^ p) ^ (-1 / p)) ^ p * (x v) ^ p := by
        apply Finset.sum_congr rfl
        intro v _
        exact Real.mul_rpow (Real.rpow_nonneg hS.le _) (hx v)
      _ = ((∑ w, (x w) ^ p) ^ (-1 / p)) ^ p * (∑ v, (x v) ^ p) :=
        (Finset.mul_sum _ _ _).symm
      _ = (∑ w, (x w) ^ p) ^ (-1 : ℝ) * (∑ v, (x v) ^ p) := by
        rw [← Real.rpow_mul hS.le]
        congr 2
        field_simp
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hS.ne']

namespace RGraph
variable {r : ℕ}

theorem polyform_zero (G : RGraph V r) (hr : 0 < r) :
    G.polyform (fun _ => 0) = 0 := by
  rw [polyform, edgePolynomial_const, zero_pow hr.ne', mul_zero, mul_zero]

theorem polyform_le_of_mass_le_one (G : RGraph V r) {p : ℝ} (hp : 0 < p)
    (hr : 0 < r) {x : V → ℝ} (hx : ∀ v, 0 ≤ x v)
    (hS : ∑ v, (x v) ^ p ≤ 1) : G.polyform x ≤ G.pSpectralRadius p := by
  have hS0 : 0 ≤ ∑ v, (x v) ^ p :=
    Finset.sum_nonneg fun v _ => Real.rpow_nonneg (hx v) p
  rcases eq_or_lt_of_le hS0 with hzero | hpos
  · have hxx : x = fun _ => 0 := by
      funext v
      have hv : (x v) ^ p ≤ 0 := by
        calc
          (x v) ^ p ≤ ∑ w, (x w) ^ p :=
            Finset.single_le_sum (fun w _ => Real.rpow_nonneg (hx w) _) (Finset.mem_univ v)
          _ = 0 := hzero.symm
      by_contra hne
      exact (not_lt_of_ge hv) (Real.rpow_pos_of_pos (lt_of_le_of_ne (hx v) (Ne.symm hne)) _)
    rw [hxx, G.polyform_zero hr]
    exact G.pSpectralRadius_nonneg hp
  · have hnorm := PWeights.normalize hp hx hpos
    have hc : 1 ≤ (∑ v, (x v) ^ p) ^ (-1 / p) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hS
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le)
    calc
      G.polyform x ≤ ((∑ v, (x v) ^ p) ^ (-1 / p)) ^ r * G.polyform x := by
        exact le_mul_of_one_le_left (G.polyform_nonneg hx) (one_le_pow₀ hc)
      _ = G.polyform (fun v => (∑ w, (x w) ^ p) ^ (-1 / p) * x v) :=
        (G.polyform_smul _ x).symm
      _ ≤ G.pSpectralRadius p := G.polyform_le_pSpectralRadius hp hnorm

theorem pSpectralRadius_pos_of_edges_nonempty [Nonempty V] (G : RGraph V r)
    {p : ℝ} (hp : 0 < p) (hG : G.edges.Nonempty) : 0 < G.pSpectralRadius p := by
  have hN : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hS : 0 < ∑ _v : V, (1 : ℝ) ^ p := by simpa using hN
  have hn := PWeights.normalize hp (x := fun _ : V => 1) (fun _ => zero_le_one) hS
  have hc : 0 < (∑ _v : V, (1 : ℝ) ^ p) ^ (-1 / p) := Real.rpow_pos_of_pos hS _
  have hpoly : 0 < G.polyform (fun _ : V => 1) := by
    rw [polyform, edgePolynomial_const]
    have hcard : 0 < (G.edges.card : ℝ) := Nat.cast_pos.mpr hG.card_pos
    positivity
  have hv : 0 < G.polyform
      (fun _ : V => (∑ _v : V, (1 : ℝ) ^ p) ^ (-1 / p) * 1) := by
    rw [G.polyform_smul]
    exact mul_pos (pow_pos hc _) hpoly
  exact hv.trans_le (G.polyform_le_pSpectralRadius hp hn)

theorem polyform_strictMono {G H : RGraph V r} (h : G.edges ⊂ H.edges)
    {x : V → ℝ} (hx : ∀ v, 0 < x v) : G.polyform x < H.polyform x := by
  have hs : G.edgePolynomial x < H.edgePolynomial x := by
    obtain ⟨e, heH, heG⟩ := Finset.exists_of_ssubset h
    apply Finset.sum_lt_sum_of_subset h.subset heH heG
    · exact Finset.prod_pos fun v _ => hx v
    · intro f _ _
      exact Finset.prod_nonneg fun v _ => (hx v).le
  exact mul_lt_mul_of_pos_left hs (by positivity : (0 : ℝ) < r.factorial)

/-- Strict subgraph monotonicity is derived from positivity of every maximizer.
The hypothesis is a reusable criterion, not an assumption of a main theorem. -/
theorem pSpectralRadius_strictMono_of_all_maximizers_pos [Nonempty V]
    {G H : RGraph V r} {p : ℝ} (hp : 0 < p) (h : G.edges ⊂ H.edges)
    (hpos : ∀ x, H.IsMaximizer p x → ∀ v, 0 < x v) :
    G.pSpectralRadius p < H.pSpectralRadius p := by
  have hle := pSpectralRadius_mono hp h.subset
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨x, hx, hmax⟩ := G.exists_maximizer hp
  have hHx : H.polyform x = H.pSpectralRadius p := by
    apply le_antisymm (H.polyform_le_pSpectralRadius hp hx)
    rw [← heq, ← hmax]
    exact polyform_mono h.subset hx.1
  have hstrict := polyform_strictMono h (hpos x ⟨hx, hHx⟩)
  rw [hmax, hHx, heq] at hstrict
  exact (lt_irrefl _ hstrict)

end RGraph
end ChromaticSpectral
