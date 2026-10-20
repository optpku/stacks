module

import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

section

variable {X Z : Scheme.{u}}
variable (h : Z ⟶ X) [QuasiCompact h]

/- Lemma 29.3.2: a quasi-compact immersion factors as an open immersion followed by a closed
immersion. -/
@[stacks 01QV] #check
  ((AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact (f := h)).mp :
    IsImmersion h → ∃ (Zbar : Scheme.{u}) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = h)

end
