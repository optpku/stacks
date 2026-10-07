module

import ReasLib.AlgebraicGeometry.Noetherian.IrreducibleComponents
import StacksCheckRecall

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 31.26.1: let `X` be a locally Noetherian scheme and let `i : Z ⟶ X` be a closed
immersion. Then the irreducible components of `Z`, viewed as subsets of `X` via `i`, form a
locally finite family in `X`. -/
@[stacks 0BE1] #check
  (AlgebraicGeometry.locallyFinite_irreducibleComponents_of_isClosedImmersion :
    ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i],
      LocallyFinite fun W : irreducibleComponents Z ↦ i.base '' (W : Set Z))
