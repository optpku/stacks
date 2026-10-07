module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.ClosedImmersion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.21: closed immersions of schemes are local on the target for the
fpqc precoverage. -/
@[stacks 02L6] #check
  (AlgebraicGeometry.IsClosedImmersion.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsClosedImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
