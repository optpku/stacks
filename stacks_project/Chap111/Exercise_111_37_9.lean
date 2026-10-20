module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DisjointClosedSubschemes
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u v

/- Exercise 111.37.9: for a graded ring `𝒜`, disjoint closed subschemes of `Proj 𝒜` given by
closed immersions `i : Z ⟶ Proj 𝒜` and `i' : Z' ⟶ Proj 𝒜`, and an isomorphism `φ : Z ⟶ Z'`,
every point `z : Z` lies in an affine open `U ⊆ Proj 𝒜` such that `i z ∈ U`, `i' (φ z) ∈ U`,
and `φ ''ᵁ (i ⁻¹ᵁ U) = i' ⁻¹ᵁ U`. -/
@[stacks 02A5] #check (AlgebraicGeometry.Proj.exists_affineOpen_image_preimage_eq :
  ∀ {A : Type u} {σ : Type v} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {Z Z' : Scheme.{u}} (i : Z ⟶ Proj 𝒜) (i' : Z' ⟶ Proj 𝒜)
    [IsClosedImmersion i] [IsClosedImmersion i'] (φ : Z ⟶ Z') [IsIso φ]
    (h_disjoint : Disjoint (Set.range i) (Set.range i')) (z : Z),
    ∃ U : (Proj 𝒜).Opens, IsAffineOpen U ∧ i z ∈ U ∧ i' (φ z) ∈ U ∧
      φ ''ᵁ (i ⁻¹ᵁ U) = i' ⁻¹ᵁ U)
