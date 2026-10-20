module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Smooth.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.18.1: the property `P(f)` given by “`f` is smooth” is smooth
local on the source. -/
@[stacks 06F2] #check
  (AlgebraicGeometry.AlgebraicSpace.Smooth.isLocalAtSourceSmooth :
    MorphismProperty.IsLocalAtSource
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Smooth S)))
