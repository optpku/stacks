module

public import stacks_project.Chap74.Lemma_74_15_1_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.15.1: the property P(f) = “f is flat” is fpqc local on the source. -/
@[stacks 06ET] #check
  (Flat.isLocalAtSourceFpqc :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
