module

public import stacks_project.Chap74.Lemma_74_17_1_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.17.1: the property `P(f)` given by “`f` is syntomic” is syntomic
local on the source. -/
@[stacks 06F0] #check
  (Syntomic.isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      (@Syntomic S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Syntomic S)))
