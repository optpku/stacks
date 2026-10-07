module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Proper
import StacksCheckRecall

universe u

/- Lemma 35.23.16: the property `P(f)` given by “`f` is proper” is local on the
target for the fpqc precoverage. -/
@[stacks 02L1] #check
  (AlgebraicGeometry.IsProper.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsProper :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
