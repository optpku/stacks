module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyClosed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FiniteType

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsProper

/-- Properness of scheme morphisms is local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsProper : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsProper
