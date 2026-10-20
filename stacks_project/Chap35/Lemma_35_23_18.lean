module

public import stacks_project.Chap35.Lemma_35_23_18_Instances
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.18: open immersions of schemes are local on the target for the
fpqc precoverage. -/
@[stacks 02L3] #check
  (AlgebraicGeometry.IsOpenImmersion.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsOpenImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
