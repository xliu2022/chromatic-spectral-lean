module

public import Mathlib

/-!
# The spectral radius of weakly colourable uniform hypergraphs

Liu and Luo (arXiv:2605.14755v1, Theorems 1.3 and 1.4) determine the unique
maximizer of the real p-spectral radius among weakly k-colourable r-graphs
of order n, for r ≥ 4, k ≥ 2, p ≥ 1 and n > (r − 1)k. A weak colouring
requires at least two colours in every edge. The extremal graph contains
every nonmonochromatic r-set of a balanced partition of the vertices.

The six declarations below give both main theorems and their equality cases,
the combined numerical bound and its equality case, the colouring criterion
(Corollary 1.5), and existence of a balanced complete reference graph.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

universe u v

/-- A finite simple r-uniform hypergraph, including the isolated vertices of its vertex type. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace RGraph
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

/-- Sum of the vertex-weight products over the unordered edges. -/
def edgePolynomial (G : RGraph V r) (x : V → ℝ) : ℝ :=
  ∑ e ∈ G.edges, ∏ v ∈ e, x v

/-- The edge polynomial multiplied by r!, as in the paper. -/
def polyform (G : RGraph V r) (x : V → ℝ) : ℝ :=
  (r.factorial : ℝ) * G.edgePolynomial x

/-- A bijection of vertex types that preserves edge membership in both directions. -/
def IsIsomorphic (G : RGraph V r) (H : RGraph W r) : Prop :=
  ∃ f : V ≃ W, ∀ e : Finset V, e ∈ G.edges ↔ e.image f ∈ H.edges

/-- Each edge contains two vertices of different colours. -/
def IsProperColoring {k : ℕ} (G : RGraph V r) (c : V → Fin k) : Prop :=
  ∀ e ∈ G.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- Existence of a weak colouring with at most k colours. -/
def Colorable (G : RGraph V r) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, G.IsProperColoring c

/-- The r-graph of all nonmonochromatic r-subsets for the specified colouring. -/
noncomputable def completeOfColoring [Fintype V] (r : ℕ) {k : ℕ}
    (c : V → Fin k) : RGraph V r where
  edges := (Finset.univ.powersetCard r).filter
    (fun e => ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v)
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

end RGraph

/-- Nonnegative weights on the unit p-sphere. -/
def PWeights {V : Type u} [Fintype V] (p : ℝ) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∑ v, (x v) ^ p = 1

/-- Values of the polyform on these weights, with zero included for the empty vertex type. -/
noncomputable def RGraph.spectralValues {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (p : ℝ) : Set ℝ :=
  insert 0 {z | ∃ x : V → ℝ, PWeights p x ∧ z = G.polyform x}

/-- The supremum of the spectral values. On the stated range this equals the maximum on the signed unit p-sphere. -/
noncomputable def RGraph.pSpectralRadius {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (p : ℝ) : ℝ :=
  sSup (G.spectralValues p)

/-- Number of vertices of a given colour. -/
noncomputable def classSize {V : Type u} [Fintype V] {k : ℕ}
    (c : V → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun v => c v = i).card

/-- The sizes of any two colour classes differ by at most one. -/
def BalancedColoring {V : Type u} [Fintype V] {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ i j, classSize c i ≤ classSize c j + 1

/-- The graph consists of all nonmonochromatic r-sets for some balanced colouring. -/
def RGraph.IsBalancedComplete {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, BalancedColoring c ∧ G = RGraph.completeOfColoring r c

/-- The bound r! (choose(n,r) − k choose(n/k,r)) n^(−r/p), with real n/k and the falling-factorial binomial coefficient. -/
noncomputable def explicitBound (r k n : ℕ) (p : ℝ) : ℝ :=
  (r.factorial : ℝ) * ((n.choose r : ℝ) - (k : ℝ) *
    Ring.choose ((n : ℝ) / (k : ℝ)) r) * (n : ℝ) ^ (-(r : ℝ) / p)

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable [Fintype V] [Fintype W] {r k : ℕ}

/-- Theorem 1.3. The balanced complete graph maximizes the p-spectral radius, with equality exactly for graphs isomorphic to it. -/
theorem RGraph.theorem_1_3 (hr : 4 ≤ r) (hk : 2 ≤ k) {p : ℝ}
    (hp : 1 ≤ p) (hn : (r - 1) * k < Fintype.card V)
    (hcard : Fintype.card V = Fintype.card W)
    (G : RGraph V r) (T : RGraph W r) (hG : G.Colorable k)
    (hT : T.IsBalancedComplete k) :
    G.pSpectralRadius p ≤ T.pSpectralRadius p ∧
      (G.pSpectralRadius p = T.pSpectralRadius p ↔ G.IsIsomorphic T) := by
  sorry

/-- Theorem 1.4. The balanced complete graph satisfies the explicit bound, with equality exactly when k divides the number of vertices. -/
theorem theorem_1_4 (G : RGraph V r) (hG : G.IsBalancedComplete k)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hN : (r - 1) * k < Fintype.card V)
    {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p ≤ explicitBound r k (Fintype.card V) p ∧
      (G.pSpectralRadius p = explicitBound r k (Fintype.card V) p ↔ k ∣ Fintype.card V) := by
  sorry

/-- Every weakly k-colourable graph in the stated range satisfies the same explicit bound. -/
theorem chromatic_explicit_bound (G : RGraph V r) (hG : G.Colorable k)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hn : (r - 1) * k < Fintype.card V)
    {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p ≤ explicitBound r k (Fintype.card V) p := by
  sorry

/-- The explicit bound is attained exactly when k divides the order and the graph is isomorphic to a balanced complete graph. -/
theorem chromatic_explicit_eq_iff (G : RGraph V r) (T : RGraph W r)
    (hG : G.Colorable k) (hT : T.IsBalancedComplete k)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hn : (r - 1) * k < Fintype.card V)
    (hcard : Fintype.card V = Fintype.card W) {p : ℝ} (hp : 1 ≤ p) :
    G.pSpectralRadius p = explicitBound r k (Fintype.card V) p ↔
      k ∣ Fintype.card V ∧ G.IsIsomorphic T := by
  sorry

/-- Corollary 1.5. A graph above the explicit threshold has no weak k-colouring. -/
theorem corollary_1_5 (G : RGraph V r) (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hn : (r - 1) * k < Fintype.card V) {p : ℝ} (hp : 1 ≤ p)
    (hspectral : explicitBound r k (Fintype.card V) p < G.pSpectralRadius p) :
    ¬ G.Colorable k := by
  sorry

/-- A balanced complete reference graph exists on every finite vertex type in the stated range. -/
theorem exists_balanced_complete (hr : 4 ≤ r) (hk : 2 ≤ k)
    (hn : (r - 1) * k < Fintype.card V) :
    ∃ T : RGraph V r, T.IsBalancedComplete k := by
  sorry

end ChromaticSpectral
