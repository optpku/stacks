module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Triangulated
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated.Kernel
public import ReasLib.CategoryTheory.MorphismProperty.Triangulated.InverseImage
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Shift

@[expose] public section

/-!
# Triangulated Localizations of Full Subcategories

This leaf supplies the triangulated structure carried by a denominator-restricted full
subcategory.  The statements are independent of derived functors: the latter only specialize
the object property `P` and the morphism property `S`.
-/

universe v u

namespace CategoryTheory

open Limits Localization MorphismProperty ObjectProperty Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (P : ObjectProperty D) [P.IsTriangulated]
  (S : MorphismProperty D)

namespace fullSubcategoryLocalizerMorphism.functor

/-- the functor underlying the full-subcategory localizer morphism is the
triangulated inclusion.  This is the Prop-valued companion to its canonical shift-comparison
bridge. -/
@[stacks 0GSL "exact restricted localizer morphism"]
noncomputable instance isTriangulated :
    (fullSubcategoryLocalizerMorphism P S).functor.IsTriangulated := sorry

end fullSubcategoryLocalizerMorphism.functor

namespace fullSubcategoryLocalizationSystem

/-- In the triangulated setting, a saturation-fixed ambient system restricts to the cone-defined
system associated to the kernel of the localized inclusion. -/
@[stacks 0GSL "saturation-fixed restricted localization systems"]
theorem eq_kernel_trW_of_isClosed [S.IsCompatibleWithTriangulation]
    (hS : (MorphismProperty.saturation (C := D)).IsClosed S) :
    fullSubcategoryLocalizationSystem P S =
      (Functor.kernel (P.ι ⋙ S.Q)).trW := sorry

/-- a saturated triangulation-compatible system restricts to the cone-defined
system associated to the kernel of the localized inclusion. -/
@[stacks 0GSL]
theorem eq_kernel_trW [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] :
    fullSubcategoryLocalizationSystem P S =
      (Functor.kernel (P.ι ⋙ S.Q)).trW := sorry

/-- the triangle-completion axiom for a denominator system restricts along a
triangulated full subcategory. -/
@[stacks 0GSL]
theorem complete₃ [S.IsCompatibleWithTriangulation]
    (T₁ T₂ : Triangle P.FullSubcategory)
    (hT₁ : T₁ ∈ distTriang P.FullSubcategory)
    (hT₂ : T₂ ∈ distTriang P.FullSubcategory)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (ha : fullSubcategoryLocalizationSystem P S a)
    (hb : fullSubcategoryLocalizationSystem P S b)
    (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), fullSubcategoryLocalizationSystem P S c ∧
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := sorry

end fullSubcategoryLocalizationSystem


end CategoryTheory
