module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.LocalAtSource

/-!
# Local finite presentation is fppf local on the source

Locally of finite presentation for morphisms of algebraic spaces is local on the
source for the fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable (S : Scheme.{u})

#check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))
      (AlgebraicGeometry.AlgebraicSpace.fppfPrecoverage S))
