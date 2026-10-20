module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Isomorphism
import StacksCheckRecall

universe u

/- Lemma 35.23.19: the property that a scheme morphism is an isomorphism is fpqc local
on the base. -/
@[stacks 02L4] #check
  (AlgebraicGeometry.Isomorphisms.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (CategoryTheory.MorphismProperty.isomorphisms AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
