module

public import ChromaticSpectral.LocalVectorBase
public import ChromaticSpectral.LocalLayerIdentity

/-! # The complete local vector smoothing certificate -/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem exists_localSmoothingWitness {C B : Finset V} {v : V}
    {c r : ℕ} {p α β : ℝ} {x : V → ℝ}
    (hCB : Disjoint C B) (hv : v ∈ C)
    (hCcard : C.card = c + 1) (hBcard : B.card = c - 1)
    (hr : 3 ≤ r) (hrc : r ≤ c) (hp : 1 ≤ p)
    (hx : ∀ w, 0 ≤ x w) (hα : 0 < α) (hβ : 0 < β)
    (hxC : ∀ w ∈ C, x w = α) (hxB : ∀ w ∈ B, x w = β)
    (hmass : (c : ℝ) * α ^ p ≤ ((c : ℝ) - 1) * β ^ p) :
    Nonempty (LocalSmoothingWitness C B v p r x) := by
  have hc : 3 ≤ c := hr.trans hrc
  have hc0 : 0 < c := by omega
  have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  have hcp : 0 < (c : ℝ) + 1 := by linarith
  have hcm : 0 < (c : ℝ) - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hθ : 0 < p⁻¹ := inv_pos.mpr hp0
  have hθ1 : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp
  have hvB : v ∉ B := fun h => Finset.disjoint_left.mp hCB hv h
  have hC' : (C.erase v).card = c := by
    rw [Finset.card_erase_of_mem hv, hCcard]
    omega
  have hB' : (insert v B).card = c := by
    rw [Finset.card_insert_of_notMem hvB, hBcard]
    omega
  let l : ℝ := α ^ p
  let h : ℝ := β ^ p
  let A : ℝ := ((c : ℝ) + 1) * l
  let D : ℝ := ((c : ℝ) - 1) * h
  let a : ℝ := A / c
  let b : ℝ := D / c
  let m : V → ℝ := localTransfer C B v (fun w => (x w) ^ p) a b
  let y : V → ℝ := fun w => (m w) ^ p⁻¹
  have hl : 0 < l := Real.rpow_pos_of_pos hα p
  have hh : 0 < h := Real.rpow_pos_of_pos hβ p
  have hA : 0 < A := mul_pos hcp hl
  have hD : 0 < D := mul_pos hcm hh
  have ha : 0 < a := div_pos hA hcpos
  have hb : 0 < b := div_pos hD hcpos
  have hlh : l ≤ h := by
    change (c : ℝ) * l ≤ ((c : ℝ) - 1) * h at hmass
    nlinarith
  have habounds : l ≤ a ∧ a ≤ h := by
    constructor
    · apply (le_div_iff₀ hcpos).2
      dsimp [A]
      nlinarith
    · apply (div_le_iff₀ hcpos).2
      dsimp [A]
      change (c : ℝ) * l ≤ ((c : ℝ) - 1) * h at hmass
      nlinarith
  have hbbounds : l ≤ b ∧ b ≤ h := by
    constructor
    · apply (le_div_iff₀ hcpos).2
      change l * (c : ℝ) ≤ ((c : ℝ) - 1) * h
      change (c : ℝ) * l ≤ ((c : ℝ) - 1) * h at hmass
      nlinarith
    · apply (div_le_iff₀ hcpos).2
      dsimp [D]
      nlinarith
  have hm0 : ∀ w, 0 ≤ m w := localTransfer_nonneg
    (fun w => Real.rpow_nonneg (hx w) p) ha.le hb.le
  have hmC : ∀ w ∈ C.erase v, m w = a := fun _ hw => localTransfer_left hw
  have hmB : ∀ w ∈ insert v B, m w = b := fun _ hw => localTransfer_right hCB hw
  have hyC : ∀ w ∈ C.erase v, y w = a ^ p⁻¹ := by
    intro w hw
    dsimp [y]
    rw [hmC w hw]
  have hyB : ∀ w ∈ insert v B, y w = b ^ p⁻¹ := by
    intro w hw
    dsimp [y]
    rw [hmB w hw]
  have hmass_old : (∑ w ∈ C ∪ B, (x w) ^ p) = A + D := by
    rw [Finset.sum_union hCB,
      sum_const_on (fun w hw => congrArg (fun z : ℝ => z ^ p) (hxC w hw)),
      sum_const_on (fun w hw => congrArg (fun z : ℝ => z ^ p) (hxB w hw)),
      hCcard, hBcard, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show 1 ≤ c by omega), Nat.cast_one]
  have hmass_local : (∑ w ∈ C ∪ B, m w) = ∑ w ∈ C ∪ B, (x w) ^ p := by
    rw [hmass_old]
    change (∑ w ∈ C ∪ B, localTransfer C B v (fun w => (x w) ^ p) a b w) = A + D
    rw [localTransfer_sum hCB hv, hC', hB']
    dsimp [a, b]
    field_simp
  have hmass_global : (∑ w, m w) = ∑ w, (x w) ^ p :=
    sum_eq_of_local_eq (fun _ hw => localTransfer_outside hv hw) hmass_local
  have hαroot : (A / ((c : ℝ) + 1)) ^ p⁻¹ = α := by
    have heq : A / ((c : ℝ) + 1) = α ^ p := by
      dsimp [A, l]
      field_simp
    rw [heq, Real.rpow_rpow_inv hα.le hp0.ne']
  have hβroot : (D / ((c : ℝ) - 1)) ^ p⁻¹ = β := by
    have heq : D / ((c : ℝ) - 1) = β ^ p := by
      dsimp [D, h]
      field_simp
    rw [heq, Real.rpow_rpow_inv hβ.le hp0.ne']
  refine ⟨{
    y := y
    nonneg := fun w => Real.rpow_nonneg (hm0 w) _
    outside_eq := ?_
    psum_eq := ?_
    full_le := ?_
    class_le := ?_
    pure_lt := ?_
  }⟩
  · intro w hw
    dsimp [y, m]
    rw [localTransfer_outside hv hw, Real.rpow_rpow_inv (hx w) hp0.ne']
  · calc
      _ = ∑ w, m w := Finset.sum_congr rfl
        (fun w _ => Real.rpow_inv_rpow (hm0 w) hp0.ne')
      _ = _ := hmass_global
  · intro s
    have hu : ∀ w ∈ C ∪ B, (x w) ^ p = l ∨ (x w) ^ p = h := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · left
        rw [hxC w hw]
      · right
        rw [hxB w hw]
    have hm : ∀ w ∈ C ∪ B, l ≤ m w ∧ m w ≤ h := by
      intro w hw
      rw [← transfer_union hv] at hw
      rcases Finset.mem_union.mp hw with hw | hw
      · rw [hmC w hw]
        exact habounds
      · rw [hmB w hw]
        exact hbbounds
    have hE := endpoint_rpow_esymm_le hl.le hlh hu hm hmass_local.symm hθ.le hθ1 s
    have heq : esymmOn (C ∪ B) s (fun w => ((x w) ^ p) ^ p⁻¹) =
        esymmOn (C ∪ B) s x :=
      esymmOn_congr (fun w _ => Real.rpow_rpow_inv (hx w) hp0.ne') s
    rw [heq] at hE
    exact hE
  · intro s
    rw [esymmOn_const_on hyC, esymmOn_const_on hxC, hC', hCcard]
    have h := constantBlock_reduce (s := s) hc0 hA.le hθ1
    rw [hαroot] at h
    exact h
  · have hAD : (c : ℝ) / ((c : ℝ) + 1) * A ≤ D := by
      have heq : (c : ℝ) / ((c : ℝ) + 1) * A = (c : ℝ) * l := by
        dsimp [A]
        field_simp
      rw [heq]
      exact hmass
    have hcross := pureCross_mass_lt hr hrc hθ hθ1 hA hAD
    rw [hαroot, hβroot] at hcross
    have hold := crossLayer_eq_esymm_sub hCB hxC hxB (show 0 < r by omega)
    have hnew := crossLayer_eq_esymm_sub (transfer_disjoint hCB v) hyC hyB
      (show 0 < r by omega)
    rw [hCcard, hBcard] at hold
    rw [hC', hB', transfer_union hv] at hnew
    rw [← hold, ← hnew]
    exact hcross

end ChromaticSpectral
