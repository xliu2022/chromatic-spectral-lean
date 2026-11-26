module

public import ChromaticSpectral.SpectralBasic
public import ChromaticSpectral.Coloring

/-! # Relabelling invariance and colour-preserving isomorphisms
Copyright (c) 2026 Xizhi Liu. Released under Apache 2.0.
-/

@[expose] public section
open scoped BigOperators
namespace ChromaticSpectral
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}
variable [DecidableEq V] [DecidableEq W] [DecidableEq U]

theorem PWeights.comp_equiv [Fintype V] [Fintype W] {p : ℝ} {x : W → ℝ}
    (hx : PWeights p x) (f : V ≃ W) : PWeights p (x ∘ f) := by
  refine ⟨fun v => hx.1 (f v), ?_⟩
  calc
    ∑ v, ((x ∘ f) v) ^ p = ∑ w, (x w) ^ p := Fintype.sum_equiv f _ _ (fun _ => rfl)
    _ = 1 := hx.2

namespace RGraph
variable {r : ℕ} {G : RGraph V r} {H : RGraph W r} {K : RGraph U r}

theorem IsIsomorphic.refl (G : RGraph V r) : G.IsIsomorphic G :=
  ⟨Equiv.refl V, by intro e; simp⟩

theorem IsIsomorphic.symm (h : G.IsIsomorphic H) : H.IsIsomorphic G := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, ?_⟩
  intro e
  simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
    Finset.image_id'] using (hf (e.image f.symm)).symm

theorem IsIsomorphic.trans (h : G.IsIsomorphic H) (h' : H.IsIsomorphic K) :
    G.IsIsomorphic K := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  refine ⟨f.trans g, ?_⟩
  intro e
  simpa only [Equiv.coe_trans, Finset.image_image] using (hf e).trans (hg (e.image f))

theorem edges_eq_image_of_isomorphism (f : V ≃ W)
    (hf : ∀ e : Finset V, e ∈ G.edges ↔ e.image f ∈ H.edges) :
    H.edges = G.edges.image (fun e => e.image f) := by
  ext e
  constructor
  · intro he
    have heq : (e.image f.symm).image f = e := by
      simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']
    exact Finset.mem_image.mpr ⟨e.image f.symm, (hf _).mpr (by rw [heq]; exact he), heq⟩
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact (hf d).mp hd

theorem edgePolynomial_eq_of_isomorphism (f : V ≃ W)
    (hf : ∀ e : Finset V, e ∈ G.edges ↔ e.image f ∈ H.edges) (x : W → ℝ) :
    G.edgePolynomial (x ∘ f) = H.edgePolynomial x := by
  unfold edgePolynomial
  rw [edges_eq_image_of_isomorphism f hf, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e _
    exact (Finset.prod_image (fun _ _ _ _ h => f.injective h)).symm
  · intro e _ d _ hed
    exact Finset.image_injective f.injective hed

theorem polyform_eq_of_isomorphism (f : V ≃ W)
    (hf : ∀ e : Finset V, e ∈ G.edges ↔ e.image f ∈ H.edges) (x : W → ℝ) :
    G.polyform (x ∘ f) = H.polyform x := by
  rw [polyform, polyform, edgePolynomial_eq_of_isomorphism f hf]

theorem IsIsomorphic.pSpectralRadius_le [Fintype V] [Fintype W]
    (h : G.IsIsomorphic H) {p : ℝ} (hp : 0 < p) :
    G.pSpectralRadius p ≤ H.pSpectralRadius p := by
  obtain ⟨f, hf⟩ := h.symm
  apply (G.pSpectralRadius_le_iff hp (H.pSpectralRadius_nonneg hp)).mpr
  intro x hx
  rw [← polyform_eq_of_isomorphism f hf x]
  exact H.polyform_le_pSpectralRadius hp (hx.comp_equiv f)

theorem IsIsomorphic.pSpectralRadius_eq [Fintype V] [Fintype W]
    (h : G.IsIsomorphic H) {p : ℝ} (hp : 0 < p) :
    G.pSpectralRadius p = H.pSpectralRadius p :=
  le_antisymm (h.pSpectralRadius_le hp) (h.symm.pSpectralRadius_le hp)

theorem complete_isomorphic_of_color_equiv [Fintype V] [Fintype W]
    {k : ℕ} (c : V → Fin k) (d : W → Fin k) (f : V ≃ W) (g : Fin k ≃ Fin k)
    (h : ∀ v, d (f v) = g (c v)) :
    (completeOfColoring r c).IsIsomorphic (completeOfColoring r d) := by
  refine ⟨f, ?_⟩
  intro e
  rw [mem_completeOfColoring, mem_completeOfColoring,
    Finset.card_image_of_injective _ f.injective]
  constructor
  · rintro ⟨he, a, ha, b, hb, hab⟩
    refine ⟨he, f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    rw [h, h]
    exact fun hh => hab (g.injective hh)
  · rintro ⟨he, a, ha, b, hb, hab⟩
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    refine ⟨he, a', ha', b', hb', ?_⟩
    rw [h, h] at hab
    exact fun hh => hab (congrArg g hh)

end RGraph
end ChromaticSpectral
