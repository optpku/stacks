module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_15_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.15: the property `P(f)` given by “`f` is an isomorphism” is fpqc
local on the base. -/
@[stacks 041Y] #check
  (AlgebraicSpace.Isomorphisms.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.isomorphisms (AlgebraicSpace S))
      (fpqcPrecoverage S))
