module

public import stacks_project.Chap74.Lemma_74_19_2_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.19.2: the property `P(f)` given by “`f` is locally quasi-finite” is
étale local on the source. -/
@[stacks 06F5] #check
  (FiniteType.locallyQuasiFiniteIsLocalAtSourceEtale :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S))
