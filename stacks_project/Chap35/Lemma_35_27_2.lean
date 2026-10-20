module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalkwise.Injective
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.27.2: the property that every map on local rings induced by a scheme
morphism is injective is local on the source for the fpqc precoverage. -/
@[stacks 036L] #check
  (AlgebraicGeometry.stalkwiseInjective_isLocalAtSourceFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (AlgebraicGeometry.stalkwise (Function.Injective ·) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
