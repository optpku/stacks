module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]

/- Lemma 29.36.11: An étale morphism is locally of finite presentation. -/
@[stacks 02GR] #check
  (AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth (f := f) :
    AlgebraicGeometry.LocallyOfFinitePresentation f)

end AlgebraicGeometry
