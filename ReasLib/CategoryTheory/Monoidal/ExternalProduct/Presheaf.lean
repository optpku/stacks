module

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# External products of presheaves

The opposite of a product is canonically equivalent to the product of opposites.  This leaf
combines that equivalence with Mathlib's external product, giving the concrete presheaf
construction used by product-site statements.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u₁ v₁ u₂ v₂ uA vA

namespace CategoryTheory.MonoidalCategory.ExternalProduct

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {A : Type uA} [Category.{vA} A] [MonoidalCategory A]

/-- Pullback of `A`-valued presheaves along the first projection `C₁ × C₂ ⥤ C₁`. -/
@[stacks 08QB "first projection inverse image for presheaves"]
abbrev left :
    (C₁ᵒᵖ ⥤ A) ⥤ ((C₁ × C₂)ᵒᵖ ⥤ A) :=
  Functor.presheafInverseImage (Prod.fst C₁ C₂) A

/-- Pullback of `A`-valued presheaves along the second projection `C₁ × C₂ ⥤ C₂`. -/
@[stacks 08QB "second projection inverse image for presheaves"]
abbrev right :
    (C₂ᵒᵖ ⥤ A) ⥤ ((C₁ × C₂)ᵒᵖ ⥤ A) :=
  Functor.presheafInverseImage (Prod.snd C₁ C₂) A

/-- The external tensor written as projection inverse images followed by the pointwise tensor
on presheaves over `C₁ × C₂`. -/
@[stacks 08QB "projection-pullback model of the presheaf external product"]
def tensorPullback :
    ((C₁ᵒᵖ ⥤ A) × (C₂ᵒᵖ ⥤ A)) ⥤ (C₁ × C₂)ᵒᵖ ⥤ A :=
  (left (C₁ := C₁) (C₂ := C₂) (A := A)).prod
      (right (C₁ := C₁) (C₂ := C₂) (A := A)) ⋙
    tensor ((C₁ × C₂)ᵒᵖ ⥤ A)

/-- The external product of `A`-valued presheaves on `C₁` and `C₂`, transported along
`(C₁ × C₂)ᵒᵖ ≌ C₁ᵒᵖ × C₂ᵒᵖ`. -/
@[stacks 08QB "external product of presheaves"]
def presheaf :
    ((C₁ᵒᵖ ⥤ A) × (C₂ᵒᵖ ⥤ A)) ⥤ (C₁ × C₂)ᵒᵖ ⥤ A :=
  externalProductBifunctor C₁ᵒᵖ C₂ᵒᵖ A ⋙
    (Functor.whiskeringLeft (C₁ × C₂)ᵒᵖ (C₁ᵒᵖ × C₂ᵒᵖ) A).obj
      (prodOpEquiv (C := C₁) (D := C₂)).functor

/-- At each object of `(C₁ × C₂)ᵒᵖ`, the external product and the tensor of the two
projection inverse images have the same value. -/
@[stacks 08QB "pointwise external product comparison"]
theorem presheafObjEq (F₁ : C₁ᵒᵖ ⥤ A) (F₂ : C₂ᵒᵖ ⥤ A)
    (X : (C₁ × C₂)ᵒᵖ) :
    ((presheaf (C₁ := C₁) (C₂ := C₂) (A := A)).obj (F₁, F₂)).obj X =
      ((tensorPullback (C₁ := C₁) (C₂ := C₂) (A := A)).obj (F₁, F₂)).obj X := sorry

/-- Objectwise identification of the external product with the tensor of the two projection
inverse images. -/
@[stacks 08QB "external product as tensor of projection inverse images"]
theorem presheafObjIsomorphic (F₁ : C₁ᵒᵖ ⥤ A) (F₂ : C₂ᵒᵖ ⥤ A) :
    IsIsomorphic
      ((presheaf (C₁ := C₁) (C₂ := C₂) (A := A)).obj (F₁, F₂))
      ((tensorPullback (C₁ := C₁) (C₂ := C₂) (A := A)).obj (F₁, F₂)) := sorry

/-- The ordinary presheaf external product is naturally the tensor of the two projection inverse
images.  This functor-level proposition records naturality in both variables without choosing a
comparison witness in the data layer. -/
@[stacks 08QB "presheaf external product comparison"]
theorem presheafIsomorphic :
    IsIsomorphic (presheaf (C₁ := C₁) (C₂ := C₂) (A := A))
      (tensorPullback (C₁ := C₁) (C₂ := C₂) (A := A)) := sorry

end CategoryTheory.MonoidalCategory.ExternalProduct
