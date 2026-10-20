module

public import ReasLib.CategoryTheory.Adjunction.FullyFaithful
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable (hL : Nonempty (L ⋙ R).FullyFaithful)
variable (hR : Nonempty (R ⋙ L).FullyFaithful)

/- Lemma 4.24.3 (1): if `L ⋙ R` is fully faithful and `L ⊣ R`, then `L` is fully faithful. -/
@[stacks 0FWV "left adjoint from a fully faithful composite"]
#check (Adjunction.FullyFaithful.left_of_comp adj hL : Nonempty L.FullyFaithful)

/- Lemma 4.24.3 (2): if `R ⋙ L` is fully faithful and `L ⊣ R`, then `R` is fully faithful. -/
@[stacks 0FWV "right adjoint from a fully faithful composite"]
#check (Adjunction.FullyFaithful.right_of_comp adj hR : Nonempty R.FullyFaithful)

end CategoryTheory.Adjunction
