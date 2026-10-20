module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType
import StacksCheckRecall

universe u

/- Lemma 35.23.12: the property `P(f)` given by “`f` is locally of finite type”
is fpqc local on the base. -/
@[stacks 02KX] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
