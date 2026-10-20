/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Limit.Basic

/-!
# Eventual properties in inverse systems of spectral spaces

This module records the eventual-stage criterion for inclusions between inverse images along
projections from a cofiltered spectral limit.
-/

@[expose] public section

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

universe u v

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I]

/-- An inclusion between pullbacks of a constructibly closed set and a constructibly open set
holds on the inverse limit exactly when it holds after one transition to the chosen stage. -/
@[stacks 0A2X]
theorem limit_projection_preimage_subset_iff_exists_stage_preimage_subset
    {X : I ⥤ TopCat.{max u v}} [∀ j : I, SpectralSpace (X.obj j)]
    {i : I} {E F : Set (X.obj i)}
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
    (hE : IsClosed[constructibleTopology (X.obj i)] E)
    (hF : IsOpen[constructibleTopology (X.obj i)] F) :
    (limit.π X i) ⁻¹' E ⊆ (limit.π X i) ⁻¹' F ↔
      ∃ (j : I) (a : j ⟶ i), (X.map a) ⁻¹' E ⊆ (X.map a) ⁻¹' F := sorry

end
