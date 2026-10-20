module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Fppf
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.12.2: the property `P(f)` given by “`f` is locally separated” is fppf
local on the base. -/
@[stacks 042F] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.LocallySeparated S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
