module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Restriction of the base of a cofibered category

If `p : F ⥤ C` is cofibered in groupoids and `P` is a full subcategory of `C`, the restriction
`p.restrictTo P` is the induced functor from the full subcategory of objects of `F` lying over
objects of `P` to `P`.
-/

@[expose] public section

universe u v uF vF

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

/-- Restriction of a functor `p : F ⥤ C` along a full subcategory of the base. The source is the
full subcategory of `F` on objects lying over selected objects of `C`. -/
def Functor.restrictTo (p : F ⥤ C) (P : ObjectProperty C) :
    (P.inverseImage p).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((P.inverseImage p).ι ⋙ p) fun x => x.property

/-- Including the restricted projection back into `C` recovers the original projection on the
restricted total category. -/
@[simp]
theorem Functor.restrictTo_comp_ι (p : F ⥤ C) (P : ObjectProperty C) :
    Functor.restrictTo p P ⋙ P.ι = (P.inverseImage p).ι ⋙ p := sorry

/-- Restriction of a cofibered-in-groupoids projection remains cofibered in groupoids. -/
instance Functor.restrictTo.isCofibered (p : F ⥤ C) (P : ObjectProperty C)
    [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (Functor.restrictTo p P).op := sorry

/-- Bundled restriction of a category cofibered in groupoids along a full subcategory of the
base. -/
def CofiberedCategoryOver.Groupoids.restrictTo
    (X : CofiberedCategoryOver.Groupoids C) (P : ObjectProperty C) :
    CofiberedCategoryOver.Groupoids P.FullSubcategory :=
  CofiberedCategoryOver.Groupoids.ofFunctor (Functor.restrictTo X.p P)

/-- The projection of the bundled restriction is the restricted projection. -/
@[simp]
theorem CofiberedCategoryOver.Groupoids.restrictTo_p
    (X : CofiberedCategoryOver.Groupoids C) (P : ObjectProperty C) :
    (CofiberedCategoryOver.Groupoids.restrictTo X P).p = Functor.restrictTo X.p P := sorry

end CategoryTheory
