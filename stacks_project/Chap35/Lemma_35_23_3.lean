module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyClosed
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.UniversallyClosed

/- Lemma 35.23.3: the property `P(f)` given by “`f` is universally closed” is
local on the target for the fpqc precoverage. -/
@[stacks 02KS] #check (AlgebraicGeometry.UniversallyClosed.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.UniversallyClosed : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

end AlgebraicGeometry.UniversallyClosed
