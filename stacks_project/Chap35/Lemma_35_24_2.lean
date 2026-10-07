module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Dominant
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 35.24.2: the property `P(f)` given by “`f` is dominant” is fppf local on the
base. -/
@[stacks 0H8J] #check
  (AlgebraicGeometry.IsDominant.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsDominant : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
