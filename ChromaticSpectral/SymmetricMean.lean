module

public import ChromaticSpectral.TwoCoordinate

/-! # Symmetric means and finite smoothing

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

variable {V : Type*} [DecidableEq V]

/-- Maclaurin's fixed-sum upper bound, including empty sets and degrees above
the number of coordinates. -/
theorem esymmOn_le_choose_mul_mean_pow {s : Finset V} {x : V → ℝ}
    (hx : ∀ v ∈ s, 0 ≤ x v) (j : ℕ) :
    esymmOn s j x ≤ (s.card.choose j : ℝ) * ((∑ v ∈ s, x v) / s.card) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hj : s.card < j + 1
      · simp [esymmOn_eq_zero_of_card_lt hj, Nat.choose_eq_zero_of_lt hj]
      have hjN : j ≤ s.card := by omega
      have hN : 0 < (s.card : ℝ) := by exact_mod_cast (show 0 < s.card by omega)
      have hS : 0 ≤ ∑ v ∈ s, x v := Finset.sum_nonneg hx
      have hdiff : 0 ≤ (s.card : ℝ) - j := sub_nonneg.mpr (by exact_mod_cast hjN)
      have hfac : 0 < (s.card : ℝ) * ((j : ℝ) + 1) := by positivity
      have hrec := esymmOn_adjacent_mean hx j
      rw [esymmOn_one] at hrec
      have hbound := mul_le_mul_of_nonneg_left ih (mul_nonneg hdiff hS)
      have hb : ((s.card : ℝ) - j) * (s.card.choose j : ℝ) =
          ((j : ℝ) + 1) * (s.card.choose (j + 1) : ℝ) := by
        have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq s.card j)
        push_cast at h
        rw [Nat.cast_sub hjN] at h
        nlinarith [h]
      have hsum : (∑ v ∈ s, x v) =
          (s.card : ℝ) * ((∑ v ∈ s, x v) / s.card) := by
        field_simp
      have he : ((s.card : ℝ) - j) * (∑ v ∈ s, x v) *
          ((s.card.choose j : ℝ) * ((∑ v ∈ s, x v) / s.card) ^ j) =
          (s.card : ℝ) * ((j : ℝ) + 1) *
            ((s.card.choose (j + 1) : ℝ) * ((∑ v ∈ s, x v) / s.card) ^ (j + 1)) := by
        calc
          _ = (s.card : ℝ) * (((s.card : ℝ) - j) * (s.card.choose j : ℝ)) *
              ((∑ v ∈ s, x v) / s.card) ^ (j + 1) := by
                nth_rw 1 [hsum]
                rw [pow_succ]
                ring
          _ = _ := by rw [hb]; ring
      rw [he] at hbound
      exact (mul_le_mul_iff_right₀ hfac).mp (hrec.trans hbound)

theorem cast_choose_succ_identity (N j : ℕ) (hj : j ≤ N) :
    ((j : ℝ) + 1) * (N.choose (j + 1) : ℝ) =
      ((N : ℝ) - j) * (N.choose j : ℝ) := by
  have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq N j)
  push_cast at h
  rw [Nat.cast_sub hj] at h
  nlinarith [h]

theorem esymmOn_variance_recurrence {s : Finset V} {x : V → ℝ} {m c : ℝ}
    (hs : s.Nonempty) (hm : 0 ≤ m) (hx : ∀ v ∈ s, m ≤ x v)
    (hc : ∑ v ∈ s, x v = (s.card : ℝ) * c) (j : ℕ) :
    ((j : ℝ) + 2) * esymmOn s (j + 2) x +
      ((s.card - 2).choose j : ℝ) * m ^ j * (∑ v ∈ s, (x v - c) ^ 2) ≤
      ((s.card : ℝ) - (j + 1)) * c * esymmOn s (j + 1) x := by
  have hN : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have h := esymmOn_gap_ge_variance hm hx hc j
  rw [esymmOn_one, hc] at h
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith [h]

theorem esymmOn_deficit_recurrence {s : Finset V} {x : V → ℝ} {m c : ℝ}
    (hs : s.Nonempty) (hm : 0 ≤ m) (hx : ∀ v ∈ s, m ≤ x v)
    (hc : ∑ v ∈ s, x v = (s.card : ℝ) * c) {j : ℕ} (hj : j + 1 ≤ s.card) :
    ((s.card : ℝ) - (j + 1)) * c *
        ((s.card.choose (j + 1) : ℝ) * c ^ (j + 1) - esymmOn s (j + 1) x) +
      ((s.card - 2).choose j : ℝ) * m ^ j * (∑ v ∈ s, (x v - c) ^ 2) ≤
      ((j : ℝ) + 2) *
        ((s.card.choose (j + 2) : ℝ) * c ^ (j + 2) - esymmOn s (j + 2) x) := by
  have h := esymmOn_variance_recurrence hs hm hx hc j
  have hb := cast_choose_succ_identity s.card (j + 1) hj
  push_cast at hb
  have he : ((j : ℝ) + 2) * ((s.card.choose (j + 2) : ℝ) * c ^ (j + 2)) =
      ((s.card : ℝ) - (j + 1)) * c * ((s.card.choose (j + 1) : ℝ) * c ^ (j + 1)) := by
    calc
      _ = (((j : ℝ) + 2) * (s.card.choose (j + 2) : ℝ)) * c ^ (j + 2) := by ring
      _ = (((s.card : ℝ) - (j + 1)) * (s.card.choose (j + 1) : ℝ)) * c ^ (j + 2) := by
        congr 1
        convert hb using 1 <;> ring
      _ = _ := by rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]; ring
  nlinarith [h, he]

/-- Quantitative Maclaurin inequality (Claim 6.6 of Liu--Luo).
The proof is a finite induction using the squared-difference identity;
no convergence theorem for repeated averaging is required. -/
theorem esymmOn_variance_deficit {s : Finset V} {x : V → ℝ} {m c : ℝ}
    (hs : 2 ≤ s.card) (hm : 0 ≤ m) (hx : ∀ v ∈ s, m ≤ x v)
    (hc : ∑ v ∈ s, x v = (s.card : ℝ) * c) (j : ℕ) :
    (1 / 2 : ℝ) * ((s.card - 2).choose j : ℝ) * m ^ j *
        (∑ v ∈ s, (x v - c) ^ 2) ≤
      (s.card.choose (j + 2) : ℝ) * c ^ (j + 2) - esymmOn s (j + 2) x := by
  have hs' : s.Nonempty := Finset.card_pos.mp (by omega)
  have hN : 0 < (s.card : ℝ) := by exact_mod_cast hs'.card_pos
  have hcm : m ≤ c := by
    have h := Finset.sum_le_sum hx
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at h
    exact (mul_le_mul_iff_right₀ hN).mp h
  have hc0 : 0 ≤ c := hm.trans hcm
  induction j with
  | zero =>
      have h := esymmOn_deficit_recurrence hs' hm hx hc (j := 0) (by omega)
      simp only [Nat.zero_add, Nat.cast_zero, Nat.choose_zero_right, Nat.choose_one_right,
        pow_zero, pow_one, mul_one, one_mul, esymmOn_one, hc, sub_self, mul_zero,
        zero_add] at h ⊢
      norm_num only [Nat.cast_one] at h ⊢
      linarith
  | succ j ih =>
      by_cases hj : s.card < j + 3
      · have hj' : s.card - 2 < j + 1 := by omega
        simp [Nat.add_assoc, Nat.choose_eq_zero_of_lt hj,
          Nat.choose_eq_zero_of_lt hj', esymmOn_eq_zero_of_card_lt hj]
      have hjN : j + 3 ≤ s.card := by omega
      let A : ℝ := (s.card : ℝ) - (j + 2)
      let B : ℝ := ((s.card - 2).choose j : ℝ) * m ^ j
      let C : ℝ := ((s.card - 2).choose (j + 1) : ℝ) * m ^ (j + 1)
      let W : ℝ := ∑ v ∈ s, (x v - c) ^ 2
      let D : ℝ := (s.card.choose (j + 2) : ℝ) * c ^ (j + 2) - esymmOn s (j + 2) x
      let E : ℝ := (s.card.choose (j + 3) : ℝ) * c ^ (j + 3) - esymmOn s (j + 3) x
      have hA : 0 ≤ A := by dsimp [A]; exact sub_nonneg.mpr (by exact_mod_cast (show j + 2 ≤ s.card by omega))
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hW : 0 ≤ W := Finset.sum_nonneg fun v _ => sq_nonneg (x v - c)
      have hi : B / 2 * W ≤ D := by
        convert ih using 1 <;> dsimp [B, W, D] <;> ring
      have hr : A * c * D + C * W ≤ ((j : ℝ) + 3) * E := by
        have hr := esymmOn_deficit_recurrence hs' hm hx hc (j := j + 1) (by omega)
        convert hr using 1 <;> dsimp [A, C, W, D, E] <;> push_cast <;>
          simp only [Nat.add_assoc] <;> ring
      have hBC : A * m * B = ((j : ℝ) + 1) * C := by
        have hb := cast_choose_succ_identity (s.card - 2) j (by omega)
        rw [Nat.cast_sub hs] at hb
        norm_num only [Nat.cast_ofNat] at hb
        dsimp [A, B, C]
        rw [pow_succ]
        calc
          _ = (((s.card : ℝ) - 2 - j) * ((s.card - 2).choose j : ℝ)) * (m ^ j * m) := by ring
          _ = _ := by rw [← hb]; ring
      have hstep : ((j : ℝ) + 3) * (C / 2 * W) ≤ ((j : ℝ) + 3) * E := by
        calc
          _ = A * m * (B / 2 * W) + C * W := by nlinarith [hBC]
          _ ≤ A * c * (B / 2 * W) + C * W := by
            gcongr
          _ ≤ A * c * D + C * W := by
            gcongr
          _ ≤ _ := hr
      have hfin : C / 2 * W ≤ E := (mul_le_mul_iff_right₀ (by positivity : 0 < (j : ℝ) + 3)).mp hstep
      simpa only [C, W, E, Nat.add_assoc, Nat.reduceAdd, div_eq_mul_inv,
        mul_assoc, mul_comm, mul_left_comm, one_mul] using hfin

theorem sum_endpoint_values {s : Finset V} {x : V → ℝ} {l h : ℝ}
    (hx : ∀ v ∈ s, x v = l ∨ x v = h) :
    ∑ v ∈ s, x v = (s.card : ℝ) * l +
      ((s.filter fun v => x v = h).card : ℝ) * (h - l) := by
  classical
  have he : ∀ v ∈ s, x v = l + if x v = h then h - l else 0 := by
    intro v hv
    by_cases hvh : x v = h
    · simp [hvh]
    · have hvl : x v = l := (hx v hv).resolve_right hvh
      rw [if_neg hvh, add_zero]
      exact hvl
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem endpoint_multiset_eq {s : Finset V} {x y : V → ℝ} {l h : ℝ}
    (hlh : l < h) (hx : ∀ v ∈ s, x v = l ∨ x v = h)
    (hy : ∀ v ∈ s, y v = l ∨ y v = h)
    (hsum : ∑ v ∈ s, x v = ∑ v ∈ s, y v) : s.val.map x = s.val.map y := by
  classical
  have hcx : ((s.filter fun v => x v = h).card : ℝ) * (h - l) =
      ((s.filter fun v => y v = h).card : ℝ) * (h - l) := by
    linarith [sum_endpoint_values hx, sum_endpoint_values hy]
  have hcard : (s.filter fun v => x v = h).card = (s.filter fun v => y v = h).card := by
    exact_mod_cast (mul_right_cancel₀ (sub_pos.mpr hlh).ne' hcx)
  apply Multiset.ext.mpr
  intro z
  simp only [Multiset.count_map, ← Finset.filter_val]
  change (s.filter fun v => z = x v).card = (s.filter fun v => z = y v).card
  by_cases hzh : z = h
  · subst z
    simpa only [eq_comm] using hcard
  by_cases hzl : z = l
  · subst z
    have ex : s.filter (fun v => l = x v) = s.filter (fun v => ¬x v = h) := by
      ext v
      by_cases hv : v ∈ s
      · rcases hx v hv with hxv | hxv <;> simp [hv, hxv, hlh.ne, hlh.ne']
      · simp [hv]
    have ey : s.filter (fun v => l = y v) = s.filter (fun v => ¬y v = h) := by
      ext v
      by_cases hv : v ∈ s
      · rcases hy v hv with hyv | hyv <;> simp [hv, hyv, hlh.ne, hlh.ne']
      · simp [hv]
    rw [ex, ey]
    have h1 := Finset.card_filter_add_card_filter_not (s := s) (fun v => x v = h)
    have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun v => y v = h)
    omega
  · have ex : s.filter (fun v => z = x v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv
      rcases hx v hv with hxv | hxv <;> simpa only [hxv] using (by assumption : z ≠ _)
    have ey : s.filter (fun v => z = y v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv
      rcases hy v hv with hyv | hyv <;> simpa only [hyv] using (by assumption : z ≠ _)
    rw [ex, ey]

theorem endpoint_esymmOn_rpow_eq {s : Finset V} {x y : V → ℝ} {l h : ℝ}
    (hlh : l ≤ h) (hx : ∀ v ∈ s, x v = l ∨ x v = h)
    (hy : ∀ v ∈ s, y v = l ∨ y v = h)
    (hsum : ∑ v ∈ s, x v = ∑ v ∈ s, y v) (θ : ℝ) (j : ℕ) :
    esymmOn s j (fun v => (x v) ^ θ) = esymmOn s j (fun v => (y v) ^ θ) := by
  rcases eq_or_lt_of_le hlh with heq | hlt
  · apply esymmOn_congr
    intro v hv
    have hxx : x v = h := (hx v hv).elim (fun H => H.trans heq) id
    have hyy : y v = h := (hy v hv).elim (fun H => H.trans heq) id
    rw [hxx, hyy]
  · have hm := endpoint_multiset_eq hlt hx hy hsum
    have hp := congrArg (fun t : Multiset ℝ => (t.map (fun a => a ^ θ)).esymm j) hm
    simpa only [Multiset.map_map, Function.comp_def, Finset.esymm_map_val, esymmOn] using hp

theorem endpoint_of_interior_card_le_one {s : Finset V} {u x : V → ℝ} {l h : ℝ}
    (hlh : l < h) (hu : ∀ v ∈ s, u v = l ∨ u v = h)
    (hx : ∀ v ∈ s, l ≤ x v ∧ x v ≤ h)
    (hsum : ∑ v ∈ s, u v = ∑ v ∈ s, x v)
    (hsmall : (s.filter fun v => l < x v ∧ x v < h).card ≤ 1) :
    ∀ v ∈ s, x v = l ∨ x v = h := by
  classical
  intro a ha
  by_contra hbad
  have hal : l < x a := lt_of_le_of_ne (hx a ha).1 (fun H => hbad (Or.inl H.symm))
  have hah : x a < h := lt_of_le_of_ne (hx a ha).2 (fun H => hbad (Or.inr H))
  have hai : a ∈ s.filter (fun v => l < x v ∧ x v < h) := Finset.mem_filter.mpr ⟨ha, hal, hah⟩
  let y : V → ℝ := Function.update x a l
  have hy : ∀ v ∈ s, y v = l ∨ y v = h := by
    intro v hv
    by_cases hva : v = a
    · subst v; simp [y]
    have hnot : ¬(l < x v ∧ x v < h) := by
      intro hvint
      have hvi : v ∈ s.filter (fun w => l < x w ∧ x w < h) := Finset.mem_filter.mpr ⟨hv, hvint⟩
      exact hva ((Finset.card_le_one.mp hsmall) v hvi a hai)
    have hvbound := hx v hv
    have hve : x v = l ∨ x v = h := by
      rcases not_and_or.mp hnot with ht | ht
      · exact Or.inl (le_antisymm (le_of_not_gt ht) hvbound.1)
      · exact Or.inr (le_antisymm hvbound.2 (le_of_not_gt ht))
    simpa only [y, Function.update_of_ne hva] using hve
  have hySum : ∑ v ∈ s, y v = (∑ v ∈ s, x v) + l - x a := by
    dsimp [y]
    rw [Finset.sum_update_of_mem ha, Finset.sdiff_singleton_eq_erase]
    linarith [Finset.sum_erase_add s x ha]
  let M : ℕ := (s.filter fun v => u v = h).card
  let Q : ℕ := (s.filter fun v => y v = h).card
  have hrel : (M : ℝ) * (h - l) = (Q : ℝ) * (h - l) + (x a - l) := by
    have h1 := sum_endpoint_values hu
    have h2 := sum_endpoint_values hy
    dsimp [M, Q]
    linarith
  by_cases hMQ : M ≤ Q
  · have hcast : (M : ℝ) ≤ Q := by exact_mod_cast hMQ
    have hh := mul_le_mul_of_nonneg_right hcast (sub_pos.mpr hlh).le
    linarith
  · have hQM : Q + 1 ≤ M := by omega
    have hcast : (Q : ℝ) + 1 ≤ M := by exact_mod_cast hQM
    have hh := mul_le_mul_of_nonneg_right hcast (sub_pos.mpr hlh).le
    nlinarith

theorem exists_outward_rpow_step {s : Finset V} {x : V → ℝ} {l h θ : ℝ}
    (hl : 0 ≤ l) (hx : ∀ v ∈ s, l ≤ x v ∧ x v ≤ h)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : ℕ)
    (hmany : 1 < (s.filter fun v => l < x v ∧ x v < h).card) :
    ∃ y : V → ℝ,
      (∀ v ∈ s, l ≤ y v ∧ y v ≤ h) ∧
      (∑ v ∈ s, y v = ∑ v ∈ s, x v) ∧
      esymmOn s j (fun v => (y v) ^ θ) ≤ esymmOn s j (fun v => (x v) ^ θ) ∧
      (s.filter fun v => l < y v ∧ y v < h).card <
        (s.filter fun v => l < x v ∧ x v < h).card := by
  classical
  obtain ⟨u, hui, v, hvi, huv⟩ := Finset.one_lt_card.mp hmany
  obtain ⟨hu, hul, huh⟩ := Finset.mem_filter.mp hui
  obtain ⟨hv, hvl, hvh⟩ := Finset.mem_filter.mp hvi
  let a : ℝ := max l (x u + x v - h)
  let b : ℝ := x u + x v - a
  let y : V → ℝ := twoUpdate x u v a b
  have hla : l ≤ a := le_max_left _ _
  have hau : a ≤ x u := max_le (hx u hu).1 (by linarith [(hx v hv).2])
  have hav : a ≤ x v := max_le (hx v hv).1 (by linarith [(hx u hu).2])
  have hbu : x u ≤ b := by dsimp [b]; linarith
  have hbv : x v ≤ b := by dsimp [b]; linarith
  have hbh : b ≤ h := by
    have ham : x u + x v - h ≤ a := le_max_right _ _
    dsimp [b]
    linarith
  have hab : a + b = x u + x v := by dsimp [b]; ring
  have he : a = l ∨ b = h := by
    by_cases hcase : x u + x v - h ≤ l
    · exact Or.inl (max_eq_left hcase)
    · right
      have ha : a = x u + x v - h := max_eq_right (le_of_not_ge hcase)
      dsimp [b]
      rw [ha]
      ring
  have hy : ∀ w ∈ s, l ≤ y w ∧ y w ≤ h := by
    intro w hw
    by_cases hwu : w = u
    · subst w
      simp only [y, twoUpdate_apply_left x huv]
      exact ⟨hla, hau.trans (hx u hu).2⟩
    by_cases hwv : w = v
    · subst w
      simp only [y, twoUpdate_apply_right]
      exact ⟨(hx u hu).1.trans hbu, hbh⟩
    rw [show y w = x w from twoUpdate_apply_of_ne x hwu hwv a b]
    exact hx w hw
  have hsum : ∑ w ∈ s, y w = ∑ w ∈ s, x w := by
    simpa only [y, sum_twoUpdate hu hv huv, hab, sub_self, add_zero]
  have hE : esymmOn s j (fun w => (y w) ^ θ) ≤ esymmOn s j (fun w => (x w) ^ θ) :=
    esymmOn_rpow_twoUpdate_le hu hv huv (fun w hw => hl.trans (hx w hw).1)
      (hl.trans hla) hau hav hbu hbv hab hθ0 hθ1 j
  have hsub : (s.filter fun w => l < y w ∧ y w < h) ⊆
      (s.filter fun w => l < x w ∧ x w < h) := by
    intro w hw
    obtain ⟨hws, hwint⟩ := Finset.mem_filter.mp hw
    by_cases hwu : w = u
    · subst w; exact hui
    by_cases hwv : w = v
    · subst w; exact hvi
    have hwx : y w = x w := twoUpdate_apply_of_ne x hwu hwv a b
    exact Finset.mem_filter.mpr ⟨hws, by simpa only [hwx] using hwint⟩
  have hne : (s.filter fun w => l < y w ∧ y w < h) ≠
      (s.filter fun w => l < x w ∧ x w < h) := by
    intro heq
    rcases he with hal | hbh'
    · have hm : u ∈ s.filter (fun w => l < y w ∧ y w < h) := heq.symm ▸ hui
      have h := (Finset.mem_filter.mp hm).2.1
      simpa only [y, twoUpdate_apply_left x huv, hal, lt_self_iff_false] using h
    · have hm : v ∈ s.filter (fun w => l < y w ∧ y w < h) := heq.symm ▸ hvi
      have h := (Finset.mem_filter.mp hm).2.2
      simpa only [y, twoUpdate_apply_right, hbh', lt_self_iff_false] using h
  exact ⟨y, hy, hsum, hE, Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)⟩

/-- An endpoint-valued vector minimizes every elementary symmetric sum of
concave coordinate powers among interval-valued vectors of the same total mass.
The proof uses a finite number of outward two-coordinate steps. -/
theorem endpoint_rpow_esymm_le {s : Finset V} {u x : V → ℝ} {l h θ : ℝ}
    (hl : 0 ≤ l) (hlh : l ≤ h) (hu : ∀ v ∈ s, u v = l ∨ u v = h)
    (hx : ∀ v ∈ s, l ≤ x v ∧ x v ≤ h)
    (hsum : ∑ v ∈ s, u v = ∑ v ∈ s, x v)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : ℕ) :
    esymmOn s j (fun v => (u v) ^ θ) ≤ esymmOn s j (fun v => (x v) ^ θ) := by
  classical
  rcases eq_or_lt_of_le hlh with heq | hlt
  · have hxe : ∀ v ∈ s, x v = l ∨ x v = h := by
      intro v hv
      right
      exact le_antisymm (hx v hv).2 (heq ▸ (hx v hv).1)
    exact (endpoint_esymmOn_rpow_eq hlh hu hxe hsum θ j).le
  · by_cases hsmall : (s.filter fun v => l < x v ∧ x v < h).card ≤ 1
    · exact (endpoint_esymmOn_rpow_eq hlh hu
        (endpoint_of_interior_card_le_one hlt hu hx hsum hsmall) hsum θ j).le
    · obtain ⟨y, hy, hysum, hE, hcount⟩ := exists_outward_rpow_step hl hx hθ0 hθ1 j
        (lt_of_not_ge hsmall)
      have h := endpoint_rpow_esymm_le hl hlh hu hy (hsum.trans hysum.symm) hθ0 hθ1 j
      exact h.trans hE
termination_by (s.filter fun v => l < x v ∧ x v < h).card
decreasing_by exact hcount

end ChromaticSpectral
