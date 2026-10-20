module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.19.3: the property `P(f)` given by “`f` is unramified” is étale
local on the source. -/
@[stacks 06F6] #check
  (AlgebraicSpace.Unramified.isLocalAtSourceEtale :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicSpace.Unramified S : MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S))
