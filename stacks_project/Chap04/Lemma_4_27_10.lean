module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.CommSq
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.MorphismProperty.LeftFraction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
variable {X X' Y Y' : C}
variable (f : X ⟶ Y) (f' : X' ⟶ Y')
variable (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
variable (hcomm : CommSq a (L.map f) (L.map f') b)

/- Lemma 4.27.10: a commutative square in a localization with a left calculus of fractions lifts
to a diagram of left fractions in the original category. -/
@[stacks 05Q3]
#check (existsCommSqLift L W f f' a b hcomm :
  Nonempty (CommSqLift L W f f' a b))

end CategoryTheory.MorphismProperty.LeftFraction
