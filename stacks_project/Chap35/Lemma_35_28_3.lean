module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.28.3: openness of the underlying map of a scheme morphism is local on the
source for the fppf precoverage. -/
@[stacks 036P] #check
  (AlgebraicGeometry.isOpenMap_isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (AlgebraicGeometry.topologically (@IsOpenMap) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
