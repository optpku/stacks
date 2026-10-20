module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.DegreeMul
public import ReasLib.RingTheory.GradedAlgebra.Veronese.Internal

/-! # The projective spectrum of a positive Veronese subring -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section veroneseInclusion

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The inclusion of the `e`-Veronese subring of a graded ring as a degree-`e`
homomorphism. -/
noncomputable def DegreeMulHom.ofInclusion (e : ℕ) (he : 1 ≤ e) :
    DegreeMulHom (GradedRing.Veronese.grading 𝒜 e) 𝒜 e :=
  DegreeMulHom.ofRingHom (GradedRing.Veronese.inclusion 𝒜 e) he
    (GradedRing.Veronese.inclusion_mem 𝒜 e)

/-- The Veronese inclusion induces the full projective spectrum as domain. -/
theorem ofInclusion_domain_eq_top (e : ℕ) (he : 1 ≤ e) :
    DegreeMulHom.domain (DegreeMulHom.ofInclusion 𝒜 e he) = ⊤ := sorry

/-- The constructed Proj morphism of the positive Veronese inclusion is an isomorphism. -/
instance ofInclusion_isIso (e : ℕ) (he : 1 ≤ e) :
    IsIso (DegreeMulHom.mapOnTarget (DegreeMulHom.ofInclusion 𝒜 e he)
        (ofInclusion_domain_eq_top 𝒜 e he)) := sorry

end veroneseInclusion

end AlgebraicGeometry
