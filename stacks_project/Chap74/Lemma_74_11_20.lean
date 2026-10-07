module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_20_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.20: the property `P(f)` given by “`f` is quasi-affine” is fpqc
local on the base. -/
@[stacks 0423] #check
  (AlgebraicSpace.QuasiAffine.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.QuasiAffine S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
