module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.2: the property `P(f)` given by “`f` is quasi-separated” is fpqc
local on the base. -/
@[stacks 041N] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.QuasiSeparated S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
