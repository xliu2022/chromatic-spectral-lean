module

public import Mathlib

/-!
# Finite uniform hypergraphs, weak colourings and edge polynomials

Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
Author: Xizhi Liu. Finite hypergraph representation follows the author's
improved-sidorenko-lean development (ba6f109bf01436ca15e55fdf5d35dbea85ffd9c9).
The spectral normalization is r! times the sum over unordered edges.
-/

@[expose] public section
open scoped BigOperators

namespace ChromaticSpectral

universe u v

structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace RGraph
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

@[ext] theorem ext {G H : RGraph V r} (h : G.edges = H.edges) : G = H := by
  cases G
  cases H
  cases h
  rfl

instance : DecidableEq (RGraph V r) := fun G H =>
  if h : G.edges = H.edges then isTrue (ext h)
  else isFalse (fun h' => h (congrArg RGraph.edges h'))

def edgePolynomial (G : RGraph V r) (x : V → ℝ) : ℝ :=
  ∑ e ∈ G.edges, ∏ v ∈ e, x v

def polyform (G : RGraph V r) (x : V → ℝ) : ℝ :=
  (r.factorial : ℝ) * G.edgePolynomial x

def IsSubgraph (G H : RGraph V r) : Prop := G.edges ⊆ H.edges

def IsIsomorphic (G : RGraph V r) (H : RGraph W r) : Prop :=
  ∃ f : V ≃ W, ∀ e : Finset V, e ∈ G.edges ↔ e.image f ∈ H.edges

def IsProperColoring {k : ℕ} (G : RGraph V r) (c : V → Fin k) : Prop :=
  ∀ e ∈ G.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def Colorable (G : RGraph V r) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, G.IsProperColoring c

noncomputable def completeOfColoring [Fintype V] (r : ℕ) {k : ℕ}
    (c : V → Fin k) : RGraph V r where
  edges := (Finset.univ.powersetCard r).filter
    (fun e => ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v)
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

end RGraph

def PWeights {V : Type u} [Fintype V] (p : ℝ) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∑ v, (x v) ^ p = 1

noncomputable def RGraph.spectralValues {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (p : ℝ) : Set ℝ :=
  insert 0 {z | ∃ x : V → ℝ, PWeights p x ∧ z = G.polyform x}

noncomputable def RGraph.pSpectralRadius {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (p : ℝ) : ℝ :=
  sSup (G.spectralValues p)

def RGraph.IsMaximizer {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (p : ℝ) (x : V → ℝ) : Prop :=
  PWeights p x ∧ G.polyform x = G.pSpectralRadius p

noncomputable def classSize {V : Type u} [Fintype V] {k : ℕ}
    (c : V → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun v => c v = i).card

def BalancedColoring {V : Type u} [Fintype V] {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ i j, classSize c i ≤ classSize c j + 1

def RGraph.IsBalancedComplete {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, BalancedColoring c ∧ G = RGraph.completeOfColoring r c

noncomputable def explicitBound (r k n : ℕ) (p : ℝ) : ℝ :=
  (r.factorial : ℝ) * ((n.choose r : ℝ) - (k : ℝ) *
    Ring.choose ((n : ℝ) / (k : ℝ)) r) * (n : ℝ) ^ (-(r : ℝ) / p)

def esymmOn {V : Type u} [DecidableEq V] (s : Finset V) (j : ℕ) (x : V → ℝ) : ℝ :=
  ∑ e ∈ s.powersetCard j, ∏ v ∈ e, x v

end ChromaticSpectral
