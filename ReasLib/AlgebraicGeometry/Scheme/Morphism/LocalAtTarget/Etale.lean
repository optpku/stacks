module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Unramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Unramified

/-!
# Target locality of étale morphisms

This file records target locality of étaleness for morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Étaleness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Etale : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Etale
