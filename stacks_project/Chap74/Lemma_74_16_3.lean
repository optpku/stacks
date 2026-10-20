module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Open.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.16.3: the property `P(f)` given by “`f` is open” is fppf local on
the source. -/
@[stacks 06EX] #check
  (AlgebraicGeometry.AlgebraicSpace.Open.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@Open S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
