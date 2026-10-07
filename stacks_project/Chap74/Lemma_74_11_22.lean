module

public import stacks_project.Chap74.Lemma_74_11_22_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.22: the property `P(f)` given by “`f` is integral” is fpqc local
on the base. -/
@[stacks 0425] #check
  (AlgebraicSpace.IsIntegralHom.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsIntegralHom S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
