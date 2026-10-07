module

public import stacks_project.Chap76.Lemma_76_48_10_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.48.10: the property `P(f)` given by “`f` is a local complete
intersection morphism” is syntomic local on the source. -/
@[stacks 0CHN] #check
  (IsLocalCompleteIntersection.isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Syntomic S)))
