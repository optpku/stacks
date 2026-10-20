module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation

/-!
# Target locality of syntomicity

This file records target locality of syntomicity for morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Syntomic

/-- Syntomicity of scheme morphisms is local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Syntomic : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Syntomic
