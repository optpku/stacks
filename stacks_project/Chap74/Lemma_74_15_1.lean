module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.15.1: the property P(f) = “f is flat” is fpqc local on the source. -/
@[stacks 06ET] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.isLocalAtSourceFpqc :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
