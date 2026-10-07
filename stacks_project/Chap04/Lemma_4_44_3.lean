module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.Pasting
import StacksCheckRecall

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.IsLocallyGroupoid B]
variable {S T X Y Z : B}
variable (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
variable (γ : j ≫ z ≅ x ≫ f ≫ g)
variable {T' X' Y' Z' : B} {z' : T' ⟶ Z'} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
variable (sq : Bicategory.PseudoPullbackCone z' (f' ≫ g'))
variable (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))

/- Lemma 4.44.3 (1): the category of outer dotted arrows is equivalent to its canonical
mapping-path factorization category. -/
@[stacks 0H1B "(1) outer comparison"]
#check (DottedArrowPasting.outerComparison.isEquivalence x j f g z γ :
  (DottedArrowPasting.outerComparison x j f g z γ).IsEquivalence)

/- Lemma 4.44.3 (2): the canonical mapping-path projection is fibred in groupoids. -/
@[stacks 0H1B "(2) fibred projection"]
#check (DottedArrow.Factorization.projectionInGroupoids sq :
  Functor.IsFibered.InGroupoids (DottedArrow.Factorization.projection sq))

/- Lemma 4.44.3 (3): the canonical comparison from dotted arrows for the corresponding left
square to the factorization fibre is an isomorphism of categories. -/
@[stacks 0H1B "(3) fibre comparison"]
#check (DottedArrow.Factorization.fiberComparison.isIso sq d :
  (DottedArrow.Factorization.fiberComparison sq d).IsIso)

end CategoryTheory
