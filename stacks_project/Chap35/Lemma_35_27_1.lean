module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.27.1: flatness of scheme morphisms is local on the source for the
fpqc precoverage. -/
@[stacks 036K] #check
  (AlgebraicGeometry.Flat.isLocalAtSourceFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Flat :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
