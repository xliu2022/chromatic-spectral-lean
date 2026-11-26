module

public import ChromaticSpectral.Coloring
public import ChromaticSpectral.SpectralTransfer

/-! # Small kernel-checked tests of the intended definitions

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu.

These checks distinguish weak hypergraph colouring from rainbow colouring,
and check the factorial normalization and real exponent in the spectral bound.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral.SemanticChecks

def twoClassesOfFour (v : Fin 8) : Fin 2 := if v.val < 4 then 0 else 1

theorem three_one_is_edge :
    ({0, 1, 2, 4} : Finset (Fin 8)) ∈
      (RGraph.completeOfColoring 4 twoClassesOfFour).edges := by
  rw [RGraph.mem_completeOfColoring]
  decide

theorem two_two_is_edge :
    ({0, 1, 4, 5} : Finset (Fin 8)) ∈
      (RGraph.completeOfColoring 4 twoClassesOfFour).edges := by
  rw [RGraph.mem_completeOfColoring]
  decide

theorem monochromatic_four_not_edge :
    ({0, 1, 2, 3} : Finset (Fin 8)) ∉
      (RGraph.completeOfColoring 4 twoClassesOfFour).edges := by
  rw [RGraph.mem_completeOfColoring]
  decide

theorem twoClassesOfFour_balanced : BalancedColoring twoClassesOfFour := by
  unfold BalancedColoring
  decide

def singleFourEdge : RGraph (Fin 4) 4 where
  edges := {Finset.univ}
  uniform := by
    intro e he
    have heq : e = Finset.univ := Finset.mem_singleton.mp he
    rw [heq]
    decide

theorem singleFourEdge_polyform_one : singleFourEdge.polyform (fun _ => 1) = 24 := by
  norm_num [RGraph.polyform, RGraph.edgePolynomial, singleFourEdge]

theorem explicitBound_divisible_lagrangian : explicitBound 4 2 8 1 = 51 / 128 := by
  rw [explicitBound_one]
  have hchoose : Ring.choose (4 : ℝ) 4 = 1 := by
    simpa using (Ring.choose_natCast (R := ℝ) 4 4)
  have hchooseNat : Nat.choose 8 4 = 70 := by decide
  norm_num [hchoose, hchooseNat]

end ChromaticSpectral.SemanticChecks
