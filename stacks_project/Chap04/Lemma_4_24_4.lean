module

public import ReasLib.CategoryTheory.Adjunction.FullyFaithful
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/- Lemma 4.24.4 (1): a left adjoint is fully faithful exactly when its unit is invertible. -/
@[stacks 07RB "left full faithfulness iff the unit is invertible"]
#check (Adjunction.FullyFaithful.left_iff_isIso_unit adj :
  Nonempty L.FullyFaithful ↔ IsIso adj.unit)

/- Lemma 4.24.4 (2): a right adjoint is fully faithful exactly when its counit is invertible. -/
@[stacks 07RB "right full faithfulness iff the counit is invertible"]
#check (Adjunction.FullyFaithful.right_iff_isIso_counit adj :
  Nonempty R.FullyFaithful ↔ IsIso adj.counit)

/- Companion functor-isomorphism forms are available without reconstructing them from the unit
or counit. -/
#check CategoryTheory.Adjunction.FullyFaithful.left_iff_id_iso_comp
#check CategoryTheory.Adjunction.FullyFaithful.right_iff_comp_iso_id

end CategoryTheory.Adjunction
