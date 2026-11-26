module

public import ChromaticSpectral.Basic

/-! # Finite elementary symmetric sums

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

variable {V : Type*} [DecidableEq V]

@[simp] theorem esymmOn_zero (s : Finset V) (x : V → ℝ) :
    esymmOn s 0 x = 1 := by simp [esymmOn]

@[simp] theorem esymmOn_one (s : Finset V) (x : V → ℝ) :
    esymmOn s 1 x = ∑ v ∈ s, x v := by
  simp [esymmOn, Finset.powersetCard_one]

theorem esymmOn_eq_zero_of_card_lt {s : Finset V} {j : ℕ}
    (h : s.card < j) (x : V → ℝ) : esymmOn s j x = 0 := by
  simp [esymmOn, Finset.powersetCard_eq_empty.mpr h]

@[simp] theorem esymmOn_empty_succ (j : ℕ) (x : V → ℝ) :
    esymmOn ∅ (j + 1) x = 0 :=
  esymmOn_eq_zero_of_card_lt (by simp) x

theorem esymmOn_congr {s : Finset V} {x y : V → ℝ}
    (h : ∀ v ∈ s, x v = y v) (j : ℕ) : esymmOn s j x = esymmOn s j y := by
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.prod_congr rfl
  intro v hv
  exact h v ((Finset.mem_powersetCard.mp he).1 hv)

theorem esymmOn_nonneg {s : Finset V} {x : V → ℝ}
    (hx : ∀ v ∈ s, 0 ≤ x v) (j : ℕ) : 0 ≤ esymmOn s j x := by
  apply Finset.sum_nonneg
  intro e he
  exact Finset.prod_nonneg fun v hv => hx v ((Finset.mem_powersetCard.mp he).1 hv)

theorem esymmOn_mono {s : Finset V} {x y : V → ℝ}
    (hx : ∀ v ∈ s, 0 ≤ x v) (hxy : ∀ v ∈ s, x v ≤ y v) (j : ℕ) :
    esymmOn s j x ≤ esymmOn s j y := by
  apply Finset.sum_le_sum
  intro e he
  exact Finset.prod_le_prod₀ (fun v hv => hx v ((Finset.mem_powersetCard.mp he).1 hv))
    (fun v hv => hxy v ((Finset.mem_powersetCard.mp he).1 hv))

theorem esymmOn_const (s : Finset V) (j : ℕ) (a : ℝ) :
    esymmOn s j (fun _ => a) = (s.card.choose j : ℝ) * a ^ j := by
  unfold esymmOn
  have h : ∀ e ∈ s.powersetCard j, (∏ _v ∈ e, a) = a ^ j := by
    intro e he
    simp [(Finset.mem_powersetCard.mp he).2]
  simp_rw [Finset.sum_congr rfl h]
  simp

theorem continuous_esymmOn (s : Finset V) (j : ℕ) :
    Continuous (esymmOn s j : (V → ℝ) → ℝ) := by
  unfold esymmOn
  fun_prop

theorem esymmOn_insert_succ {s : Finset V} {v : V} (hv : v ∉ s)
    (j : ℕ) (x : V → ℝ) :
    esymmOn (insert v s) (j + 1) x = esymmOn s (j + 1) x + x v * esymmOn s j x := by
  unfold esymmOn
  rw [Finset.powersetCard_succ_insert hv]
  have hdis : Disjoint (s.powersetCard (j + 1)) ((s.powersetCard j).image (insert v)) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he'
    exact hv ((Finset.mem_powersetCard.mp he).1 (Finset.mem_insert_self _ _))
  rw [Finset.sum_union hdis, Finset.sum_image]
  · congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact Finset.prod_insert (fun h => hv ((Finset.mem_powersetCard.mp he).1 h))
  · intro a ha b hb hab
    have hva : v ∉ a := fun h => hv ((Finset.mem_powersetCard.mp ha).1 h)
    have hvb : v ∉ b := fun h => hv ((Finset.mem_powersetCard.mp hb).1 h)
    simpa only [Finset.erase_insert hva, Finset.erase_insert hvb] using
      congrArg (fun t : Finset V => t.erase v) hab

theorem esymmOn_erase_succ {s : Finset V} {v : V} (hv : v ∈ s)
    (j : ℕ) (x : V → ℝ) :
    esymmOn s (j + 1) x = esymmOn (s.erase v) (j + 1) x + x v * esymmOn (s.erase v) j x := by
  simpa only [Finset.insert_erase hv] using esymmOn_insert_succ (Finset.notMem_erase v s) j x

theorem esymmOn_erase_pair {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (j : ℕ) (x : V → ℝ) :
    esymmOn (s.erase u) (j + 1) x =
      esymmOn ((s.erase u).erase v) (j + 1) x +
        x v * esymmOn ((s.erase u).erase v) j x :=
  esymmOn_erase_succ (Finset.mem_erase.mpr ⟨hne.symm, hv⟩) j x

theorem esymmOn_erase_sub {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (j : ℕ) (x : V → ℝ) :
    esymmOn (s.erase u) (j + 1) x - esymmOn (s.erase v) (j + 1) x =
      (x v - x u) * esymmOn ((s.erase u).erase v) j x := by
  rw [esymmOn_erase_pair hu hv hne, esymmOn_erase_pair hv hu hne.symm]
  have he : (s.erase v).erase u = (s.erase u).erase v := by ext; simp [and_left_comm]
  rw [he]
  ring

theorem sum_esymmOn_erase (s : Finset V) (j : ℕ) (x : V → ℝ) :
    ∑ v ∈ s, esymmOn (s.erase v) j x = ((s.card : ℝ) - j) * esymmOn s j x := by
  induction s using Finset.induction_on generalizing j with
  | empty =>
      cases j with
      | zero => simp
      | succ j => simp
  | @insert a s ha ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [Finset.sum_insert ha, Finset.erase_insert ha]
          have he : ∀ v ∈ s, (insert a s).erase v = insert a (s.erase v) := by
            intro v hv
            exact Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv ha).symm
          simp_rw [Finset.sum_congr rfl (fun v hv => congrArg (fun t => esymmOn t (j + 1) x) (he v hv))]
          have hi : ∀ v ∈ s, esymmOn (insert a (s.erase v)) (j + 1) x =
              esymmOn (s.erase v) (j + 1) x + x a * esymmOn (s.erase v) j x := by
            intro v hv
            exact esymmOn_insert_succ (fun h => ha (Finset.mem_of_mem_erase h)) j x
          rw [Finset.sum_congr rfl hi, Finset.sum_add_distrib, ← Finset.mul_sum,
            ih (j + 1), ih j, esymmOn_insert_succ ha, Finset.card_insert_of_notMem ha]
          push_cast
          ring

theorem sum_mul_esymmOn_erase (s : Finset V) (j : ℕ) (x : V → ℝ) :
    ∑ v ∈ s, x v * esymmOn (s.erase v) j x = ((j : ℝ) + 1) * esymmOn s (j + 1) x := by
  induction s using Finset.induction_on generalizing j with
  | empty => simp
  | @insert a s ha ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [Finset.sum_insert ha, Finset.erase_insert ha]
          have hi : ∀ v ∈ s, x v * esymmOn ((insert a s).erase v) (j + 1) x =
              x v * esymmOn (s.erase v) (j + 1) x +
                x a * (x v * esymmOn (s.erase v) j x) := by
            intro v hv
            rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv ha).symm,
              esymmOn_insert_succ (fun h => ha (Finset.mem_of_mem_erase h))]
            ring
          rw [Finset.sum_congr rfl hi, Finset.sum_add_distrib, ← Finset.mul_sum,
            ih (j + 1), ih j, esymmOn_insert_succ ha]
          push_cast
          ring

theorem esymmOn_erase_antivary {s : Finset V} {x : V → ℝ}
    (hx : ∀ v ∈ s, 0 ≤ x v) (j : ℕ) :
    AntivaryOn x (fun v => esymmOn (s.erase v) j x) s := by
  apply AntivaryOn.symm
  intro u hu v hv huv
  cases j with
  | zero => simp
  | succ j =>
      have hne : u ≠ v := by intro h; subst v; exact lt_irrefl _ huv
      have he := esymmOn_erase_sub hu hv hne j x
      have hn := esymmOn_nonneg
        (s := (s.erase u).erase v)
        (fun w hw => hx w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))) j
      have hp := mul_nonneg (sub_nonneg.mpr huv.le) hn
      linarith

/-- The adjacent mean inequality for elementary symmetric sums, with no division.
This includes the zero-degree and above-cardinality cases. -/
theorem esymmOn_adjacent_mean {s : Finset V} {x : V → ℝ}
    (hx : ∀ v ∈ s, 0 ≤ x v) (j : ℕ) :
    (s.card : ℝ) * ((j : ℝ) + 1) * esymmOn s (j + 1) x ≤
      ((s.card : ℝ) - j) * esymmOn s 1 x * esymmOn s j x := by
  have h := (esymmOn_erase_antivary hx j).card_mul_sum_le_sum_mul_sum
  rw [sum_mul_esymmOn_erase, sum_esymmOn_erase, ← esymmOn_one] at h
  nlinarith [h]

end ChromaticSpectral
