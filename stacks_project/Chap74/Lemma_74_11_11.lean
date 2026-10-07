module

public import stacks_project.Chap74.Lemma_74_11_11_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.11: the property `P(f)` given by “`f` is of finite type” is fpqc
local on the base. -/
@[stacks 041U] #check
  (AlgebraicSpace.FiniteType.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.FiniteType S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
