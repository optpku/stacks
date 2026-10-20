module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOneCover
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy

/-!
# Relative twists under degree-one generation

Affine-local generation in degree one makes every integral relative twist invertible and every
canonical multiplication morphism between relative twists an isomorphism.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

/-- Every integral twist in a relative projective presentation is invertible when all affine
graded models are generated in degree one. -/
theorem twist_invertible_of_generatedByDegreeOne
    {S : Scheme.{u}}
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
    {X : Scheme.{u}} {π : X ⟶ S}
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    (hgenerated : ∀ U : S.affineOpens,
      GradedAlgebra.GeneratedBy (sectionGrading U) 1)
    (n : ℤ) :
    Scheme.Modules.Invertible (presentation.twistAlgebra n) := sorry

/-- The canonical multiplication morphism between any two integral twists in a relative
projective presentation is an isomorphism when all affine graded models are generated in
degree one. -/
theorem mulHom_isIso_of_generatedByDegreeOne
    {S : Scheme.{u}}
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
    {X : Scheme.{u}} {π : X ⟶ S}
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    (hgenerated : ∀ U : S.affineOpens,
      GradedAlgebra.GeneratedBy (sectionGrading U) 1)
    (a b : ℤ) :
    IsIso (GradedAlgebraSheaf.mulHom presentation.twistAlgebra a b) := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
