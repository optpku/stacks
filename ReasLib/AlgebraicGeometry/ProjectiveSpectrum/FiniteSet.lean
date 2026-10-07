module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

@[expose] public section

open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Proj

/-- Every finite set of points of a projective spectrum is contained in a standard affine
open defined by a homogeneous element of positive degree. -/
theorem exists_basicOpen_containing_finiteSet {A : Type u} {σ : Type v} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (E : Set (Proj 𝒜)) (hE : E.Finite) :
    ∃ (d : ℕ) (hd : 0 < d) (f : A) (hf : f ∈ 𝒜 d), E ⊆ Proj.basicOpen 𝒜 f := sorry

end AlgebraicGeometry.Proj
