module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AtWorstNodal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 53.20.8: at-worst-nodality of relative dimension one is local on the source
for the étale precoverage. -/
@[stacks 0C5D] #check
  (AlgebraicGeometry.AtWorstNodal.isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.AtWorstNodal :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)
