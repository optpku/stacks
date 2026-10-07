module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Surjective
import StacksCheckRecall

universe u

/- Lemma 35.23.7: the property `P(f)` given by “`f` is surjective” is fpqc local
on the base. -/
@[stacks 02KV] #check
  (AlgebraicGeometry.Surjective.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Surjective :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
