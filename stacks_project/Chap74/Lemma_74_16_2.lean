module

public import stacks_project.Chap74.Lemma_74_16_2_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.16.2: the property `P(f)` given by “`f` is locally of finite
type” is fppf local on the source. -/
@[stacks 06EW] #check
  (LocallyOfFiniteType.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
