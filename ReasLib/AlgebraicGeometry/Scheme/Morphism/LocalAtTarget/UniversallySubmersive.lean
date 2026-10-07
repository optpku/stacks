module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.UniversallySubmersive

/-- Universal submersiveness of scheme morphisms is local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.UniversallySubmersive :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.UniversallySubmersive
