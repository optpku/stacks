module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

variable (X : Scheme.{u})

/- Definition 29.47.8: The structure map of the initial object in `SeminormalizationOver X`
is the seminormalization of `X`, and the structure map of the initial object in
`AbsoluteWeakNormalizationOver X` is the absolute weak normalization of `X`. -/

@[stacks 0EUT]
#check ((⊥_ (SeminormalizationOver X)).1.hom :
    (⊥_ (SeminormalizationOver X)).1.left ⟶ X)

#check ((⊥_ (AbsoluteWeakNormalizationOver X)).1.hom :
    (⊥_ (AbsoluteWeakNormalizationOver X)).1.left ⟶ X)

end

end AlgebraicGeometry.Scheme
