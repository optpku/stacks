module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.2.6 (1): being a thickening is local on the target for the fpqc precoverage. -/
@[stacks 0BPF]
#check (AlgebraicGeometry.IsThickening.isLocalAtTargetFpqc :
  MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.IsThickening : MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 37.2.6 (2): being a first-order thickening is local on the target for the fpqc
precoverage. -/
@[stacks 0BPF]
#check (AlgebraicGeometry.IsFirstOrderThickening.isLocalAtTargetFpqc :
  MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.IsFirstOrderThickening :
      MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
