module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Proj

/-- Disjoint isomorphic closed subschemes of a projective spectrum admit a common affine
open neighborhood of every pair of corresponding points, whose inverse images agree under
the isomorphism. -/
@[stacks 02A5]
theorem exists_affineOpen_image_preimage_eq {A : Type u} {σ : Type v} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {Z Z' : Scheme.{u}} (i : Z ⟶ Proj 𝒜) (i' : Z' ⟶ Proj 𝒜)
    [IsClosedImmersion i] [IsClosedImmersion i'] (φ : Z ⟶ Z') [IsIso φ]
    (h_disjoint : Disjoint (Set.range i) (Set.range i')) (z : Z) :
    ∃ U : (Proj 𝒜).Opens, IsAffineOpen U ∧ i z ∈ U ∧ i' (φ z) ∈ U ∧
      φ ''ᵁ (i ⁻¹ᵁ U) = i' ⁻¹ᵁ U := sorry

end AlgebraicGeometry.Proj
