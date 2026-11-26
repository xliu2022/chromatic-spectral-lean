module

public import ChromaticSpectral.Positivity
public import ChromaticSpectral.ClassMove

/-! # Two-coordinate stationarity across different colour classes
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators Topology
namespace ChromaticSpectral
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {k : ℕ}

theorem esymmOn_twoUpdate_one_sub {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∉ s) (j : ℕ) (x : V → ℝ) (a b : ℝ) :
    esymmOn s (j + 1) (twoUpdate x u v a b) - esymmOn s (j + 1) x =
      (a - x u) * esymmOn (s.erase u) j x := by
  have hne : u ≠ v := by intro h; subst v; exact hv hu
  have hrest (d : ℕ) : esymmOn (s.erase u) d (twoUpdate x u v a b) =
      esymmOn (s.erase u) d x := by
    apply esymmOn_congr
    intro w hw
    exact twoUpdate_apply_of_ne x (Finset.mem_erase.mp hw).1
      (by intro h; subst w; exact hv (Finset.mem_of_mem_erase hw)) a b
  rw [esymmOn_erase_succ hu, esymmOn_erase_succ hu,
    hrest, hrest, twoUpdate_apply_left x hne]
  ring

theorem twoUpdate_comm (x : V → ℝ) {u v : V} (hne : u ≠ v) (a b : ℝ) :
    twoUpdate x u v a b = twoUpdate x v u b a := by
  funext w
  by_cases hwu : w = u
  · subst w; simp [twoUpdate, hne]
  · by_cases hwv : w = v
    · subst w; simp [twoUpdate, hne.symm]
    · simp [twoUpdate, hwu, hwv]

theorem RGraph.complete_twoUpdate_cross_sub (c : V → Fin k) (x : V → ℝ)
    {u v : V} (hc : c u ≠ c v) (j : ℕ) (a b : ℝ) :
    (completeOfColoring (j + 2) c).edgePolynomial (twoUpdate x u v a b) -
      (completeOfColoring (j + 2) c).edgePolynomial x =
      (a + b - (x u + x v)) * esymmOn ((Finset.univ.erase u).erase v) (j + 1) x +
      (a * b - x u * x v) * esymmOn ((Finset.univ.erase u).erase v) j x -
      (a - x u) * esymmOn ((classSet c (c u)).erase u) (j + 1) x -
      (b - x v) * esymmOn ((classSet c (c v)).erase v) (j + 1) x := by
  have hne : u ≠ v := fun h => hc (congrArg c h)
  have hfull := esymmOn_twoUpdate_sub (Finset.mem_univ u) (Finset.mem_univ v) hne j x a b
  have hu : u ∈ classSet c (c u) := by simp
  have hv : v ∈ classSet c (c v) := by simp
  have hvnot : v ∉ classSet c (c u) := by simpa using hc.symm
  have hunot : u ∉ classSet c (c v) := by simpa using hc
  have hsource := esymmOn_twoUpdate_one_sub hu hvnot (j + 1) x a b
  have htarget := esymmOn_twoUpdate_one_sub hv hunot (j + 1) x b a
  rw [← twoUpdate_comm x hne a b] at htarget
  have hsum := sum_sub_eq_pair
    (fun i => esymmOn (classSet c i) (j + 2) (twoUpdate x u v a b))
    (fun i => esymmOn (classSet c i) (j + 2) x) hc
    (by
      intro i hi hiv
      apply esymmOn_congr
      intro w hw
      have hwi := (mem_classSet c i w).mp hw
      exact twoUpdate_apply_of_ne x
        (by intro h; subst w; exact hi hwi.symm)
        (by intro h; subst w; exact hiv hwi.symm) a b)
  rw [complete_edgePolynomial c (by omega), complete_edgePolynomial c (by omega)]
  linear_combination hfull - hsum - hsource - htarget

theorem RGraph.complete_maximizer_link_difference [Nonempty V]
    {r : ℕ} (hr : 3 ≤ r) (c : V → Fin k)
    (hQ : (completeOfColoring r c).edges.Nonempty) {x : V → ℝ}
    (hx : (completeOfColoring r c).IsMaximizer 1 x)
    {u v : V} (hc : c u ≠ c v) :
    (x v - x u) * esymmOn ((Finset.univ.erase u).erase v) (r - 2) x -
      esymmOn ((classSet c (c u)).erase u) (r - 1) x +
      esymmOn ((classSet c (c v)).erase v) (r - 1) x = 0 := by
  have hpos := complete_maximizer_pos hr c (by norm_num) hQ hx
  have hne : u ≠ v := fun h => hc (congrArg c h)
  let C := esymmOn ((Finset.univ.erase u).erase v) (r - 2) x
  let D := (x v - x u) * C - esymmOn ((classSet c (c u)).erase u) (r - 1) x +
    esymmOn ((classSet c (c v)).erase v) (r - 1) x
  let q : ℝ → ℝ := fun t => (completeOfColoring r c).edgePolynomial x + t * D - t ^ 2 * C
  have hchange (t : ℝ) : (completeOfColoring r c).edgePolynomial
      (twoUpdate x u v (x u + t) (x v - t)) = q t := by
    have hh := complete_twoUpdate_cross_sub c x hc (r - 2) (x u + t) (x v - t)
    have hr2 : r - 2 + 2 = r := by omega
    have hr1 : r - 2 + 1 = r - 1 := by omega
    rw [hr2, hr1] at hh
    dsimp [q, D, C]
    linear_combination hh
  have hmax : IsLocalMax q 0 := by
    filter_upwards [Ioo_mem_nhds (show -x u < 0 by linarith [hpos u]) (hpos v)] with t ht
    have hy : PWeights 1 (twoUpdate x u v (x u + t) (x v - t)) := by
      constructor
      · intro w
        by_cases hwu : w = u
        · subst w; rw [twoUpdate_apply_left x hne]; linarith [ht.1]
        · by_cases hwv : w = v
          · subst w; rw [twoUpdate_apply_right]; linarith [ht.2]
          · rw [twoUpdate_apply_of_ne x hwu hwv]; exact hx.1.1 w
      · simp only [Real.rpow_one]
        have hsum := sum_comp_twoUpdate id x hne (x u + t) (x v - t)
        have hxsum : ∑ w, x w = 1 := by simpa only [Real.rpow_one] using hx.1.2
        dsimp only [id_eq] at hsum
        linarith
    have hP := (completeOfColoring r c).polyform_le_pSpectralRadius (by norm_num) hy
    rw [← hx.2] at hP
    unfold polyform at hP
    have hf : (0 : ℝ) < r.factorial := by positivity
    have hE : (completeOfColoring r c).edgePolynomial
        (twoUpdate x u v (x u + t) (x v - t)) ≤ (completeOfColoring r c).edgePolynomial x := by
      nlinarith
    rw [hchange] at hE
    simpa only [q, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] using hE
  have hd : HasDerivAt q D 0 := by
    convert ((hasDerivAt_const 0 ((completeOfColoring r c).edgePolynomial x)).add
      ((hasDerivAt_id 0).mul_const D)).sub (((hasDerivAt_id 0).pow 2).mul_const C) using 1 <;>
      simp [q] <;> rfl
  exact hd.deriv.symm.trans hmax.deriv_eq_zero

end ChromaticSpectral
