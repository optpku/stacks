module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Local finite presentation is fpqc local on the target

Locally of finite presentation for morphisms of algebraic spaces is local on the
target for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces is local on the
target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation
