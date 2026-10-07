module

public import stacks_project.Chap74.Lemma_74_11_21_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.21: the property `P(f)` given by “`f` is a quasi-compact immersion”
is fpqc local on the base. -/
@[stacks 0424] #check
  (AlgebraicSpace.QuasiCompactImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.QuasiCompact S ⊓ @AlgebraicSpace.IsImmersion S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
