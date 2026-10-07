module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocalCompleteIntersection
import StacksCheckRecall

universe u

/- Lemma 37.62.19: the property that a scheme morphism is a local complete intersection
morphism is local on the target for the fpqc precoverage. -/
@[stacks 069N] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
