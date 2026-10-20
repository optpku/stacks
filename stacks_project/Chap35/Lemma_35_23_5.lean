module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallySubmersive
import StacksCheckRecall

universe u

/- Lemma 35.23.5: the property `P(f)` given by “`f` is universally submersive” is
fpqc local on the base. -/
@[stacks 0CEW] #check
  (AlgebraicGeometry.UniversallySubmersive.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.UniversallySubmersive :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
