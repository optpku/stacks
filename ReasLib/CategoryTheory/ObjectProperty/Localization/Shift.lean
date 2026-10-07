module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Shift
public import ReasLib.CategoryTheory.MorphismProperty.Shift.InverseImage
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory

@[expose] public section

/-!
# Shifts on Localizations of Full Subcategories

This facade combines the full-subcategory inclusion with the generic inverse-image theorem for
shift-compatible morphism properties.  Typeclass search therefore supplies shift compatibility
of `fullSubcategoryLocalizationSystem P S` and commutation with shifts of the induced localized
functor, including shift compatibility of its canonical comparison, without parallel
full-subcategory-specific instances.
-/

namespace CategoryTheory

universe v u w

open ObjectProperty

variable {D : Type u} [Category.{v} D]
  {A : Type w} [AddMonoid A] [HasShift D A]
  (P : ObjectProperty D) (S : MorphismProperty D)

namespace fullSubcategoryLocalizerMorphism.functor

/-- the functor underlying the full-subcategory localizer morphism carries the
canonical shift comparison of the inclusion.  This bridge is needed because the inclusion's
shift instance is deliberately irreducible in Mathlib. -/
@[stacks 0GSL "shift comparison for the restricted localizer morphism"]
noncomputable instance commShift [P.IsStableUnderShift A] :
    (fullSubcategoryLocalizerMorphism P S).functor.CommShift A :=
  inferInstanceAs (P.ι.CommShift A)

end fullSubcategoryLocalizerMorphism.functor

end CategoryTheory
