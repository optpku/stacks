module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.RegularImmersion
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 35.23.34 (1): the property that a scheme morphism is a Koszul-regular
immersion is fpqc local on the base. -/
@[stacks 0694] #check
  (AlgebraicGeometry.IsKoszulRegularImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 35.23.34 (2): the property that a scheme morphism is an `H₁`-regular
immersion is fpqc local on the base. -/
@[stacks 0694] #check
  (AlgebraicGeometry.IsH1RegularImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsH1RegularImmersion f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 35.23.34 (3): the property that a scheme morphism is a quasi-regular
immersion is fpqc local on the base. -/
@[stacks 0694] #check
  (AlgebraicGeometry.IsQuasiRegularImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsQuasiRegularImmersion f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
