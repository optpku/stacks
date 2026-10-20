module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces is local on the
source for the fppf precoverage. -/
instance isLocalAtSourceFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation
