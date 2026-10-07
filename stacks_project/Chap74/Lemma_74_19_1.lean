module

public import stacks_project.Chap74.Lemma_74_19_1_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.19.1: the property `P(f)` given by “`f` is étale” is étale
local on the source. -/
@[stacks 06F4] #check
  (AlgebraicSpace.Etale.isLocalAtSourceEtale :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicSpace.Etale S : MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S))
