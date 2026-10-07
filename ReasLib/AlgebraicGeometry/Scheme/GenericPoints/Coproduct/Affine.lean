module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.RingTheory.Localization.TotalQuotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic-point coproducts over affine opens

The map from a scheme to the coproduct of the spectra of its generic-point
residue fields gives an explicit algebra structure on sections over the
preimage of an affine open. For a reduced scheme with finitely many components
on compact opens, these sections form the total quotient ring.
-/

@[expose] public section

open scoped AlgebraicGeometry nonZeroDivisors
open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace GenericPointCoproduct.Affine

/-- The algebra structure on sections over an affine preimage induced by the
generic-point coproduct morphism. -/
@[reducible]
noncomputable instance sectionsAlgebra
    {X : Scheme.{u}} (U : X.affineOpens) :
    Algebra Γ(X, (U : X.Opens))
      Γ(genericPointSpectrumCoproduct X,
        genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens)) :=
  ((genericPointSpectrumCoproductTo X).app (U : X.Opens)).hom.toAlgebra

/-- The algebra map on affine-preimage sections is the map on sections induced
by the generic-point coproduct morphism. -/
theorem algebraMap_apply
    {X : Scheme.{u}} (U : X.affineOpens) :
    @algebraMap Γ(X, (U : X.Opens))
        Γ(genericPointSpectrumCoproduct X,
          genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens))
        _ _ (sectionsAlgebra U) =
      ((genericPointSpectrumCoproductTo X).app (U : X.Opens)).hom := sorry

/-- Over a reduced scheme with finitely many components on compact opens,
sections of the generic-point coproduct over an affine open are a localization
of the affine section ring at its nonzerodivisors. -/
@[stacks 035P]
instance sectionsIsLocalization {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    @IsLocalization Γ(X, (U : X.Opens)) _
      (nonZeroDivisors Γ(X, (U : X.Opens)))
      Γ(genericPointSpectrumCoproduct X,
        genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens)) _
      (sectionsAlgebra U) := sorry

namespace TotalQuotient

/-- The ring of sections over the generic-point coproduct preimage of an affine open
in a reduced scheme with finitely many irreducible components on compact opens is
its total quotient ring. -/
@[stacks 035P]
noncomputable def sectionsEquiv
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    Γ(genericPointSpectrumCoproduct X,
        genericPointSpectrumCoproductTo X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      Localization.totalQuotientRing Γ(X, U) :=
  IsLocalization.algEquiv (nonZeroDivisors Γ(X, U)) _ _

/-- The integral closure in the total quotient ring agrees with the integral
closure in sections over the affine preimage in the generic-point coproduct. -/
@[stacks 035P]
noncomputable def integralClosureEquiv
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    integralClosure Γ(X, U)
        Γ(genericPointSpectrumCoproduct X,
          genericPointSpectrumCoproductTo X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (Localization.totalQuotientRing Γ(X, U)) :=
  (sectionsEquiv U).mapIntegralClosure

/-- The preimage of an affine open in the normalization is the spectrum of the
integral closure of its section ring in its total quotient ring. -/
@[stacks 035P]
noncomputable def normalizationPreimageIso
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X) ⁻¹ᵁ
        (U : X.Opens)).toScheme ≅
      Spec (CommRingCat.of (integralClosure Γ(X, U)
        (Localization.totalQuotientRing Γ(X, U)))) :=
  (U.2.preimage
      (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X))).isoSpec ≪≫
    (Scheme.Spec.mapIso (Scheme.Hom.normalizationObjIso
      (genericPointSpectrumCoproductTo X) U.2).op).symm ≪≫
    (Scheme.Spec.mapIso
      (integralClosureEquiv U).toRingEquiv.toCommRingCatIso.op).symm

end TotalQuotient

end GenericPointCoproduct.Affine

end AlgebraicGeometry
