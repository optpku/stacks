module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Immersion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.24.1: the property `P(f)` given by “`f` is an immersion” is local on the
target for the fppf precoverage. -/
@[stacks 02YM] #check
  (AlgebraicGeometry.IsImmersion.isLocalAtTargetFppf :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
