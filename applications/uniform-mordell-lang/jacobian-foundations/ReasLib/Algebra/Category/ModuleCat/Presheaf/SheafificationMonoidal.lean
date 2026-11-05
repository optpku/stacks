module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidal comparisons for module-presheaf sheafification

This leaf owns the tensor comparison API induced by an explicitly supplied
monoidal structure on module sheafification.  It is stated for arbitrary ring
presheaves and ring sheaves, so geometric specializations only need thin views.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ RingCat.{max u v}} {R : Sheaf J RingCat.{max u v}}
variable (α : R₀ ⟶ R.obj)
variable [Presheaf.IsLocallyInjective J α]
variable [Presheaf.IsLocallySurjective J α]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [MonoidalCategory (PresheafOfModules R₀)]
variable [MonoidalCategory (SheafOfModules R)]
variable [Functor.Monoidal (sheafification α)]

/-- The tensor comparison from the tensor product of two sheafified module presheaves to the
sheafification of their tensor product. -/
noncomputable abbrev sheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules R₀) :
    CategoryTheory.MonoidalCategory.tensorObj
        ((sheafification α).obj ℱ)
        ((sheafification α).obj 𝒢) ≅
      (sheafification α).obj
        (CategoryTheory.MonoidalCategory.tensorObj ℱ 𝒢) :=
  Functor.Monoidal.μIso (sheafification α) ℱ 𝒢

/-- The oplax tensor comparison from sheafification of a tensor product to the tensor product of
the two sheafifications. -/
noncomputable abbrev sheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules R₀) :
    (sheafification α).obj
        (CategoryTheory.MonoidalCategory.tensorObj ℱ 𝒢) ⟶
      CategoryTheory.MonoidalCategory.tensorObj
        ((sheafification α).obj ℱ)
        ((sheafification α).obj 𝒢) :=
  (sheafificationTensorIso α ℱ 𝒢).inv

/-- Module sheafification commutes with right tensoring through its supplied monoidal
comparison. -/
noncomputable abbrev sheafificationTensorRightIso
    (ℱ : PresheafOfModules R₀) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ sheafification α ≅
      sheafification α ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((sheafification α).obj ℱ) :=
  (Functor.Monoidal.commTensorRight (sheafification α) ℱ).symm

/-- Module sheafification commutes with left tensoring through its supplied monoidal
comparison. -/
noncomputable abbrev sheafificationTensorLeftIso
    (ℱ : PresheafOfModules R₀) :
    CategoryTheory.MonoidalCategory.tensorLeft ℱ ⋙ sheafification α ≅
      sheafification α ⋙
        CategoryTheory.MonoidalCategory.tensorLeft ((sheafification α).obj ℱ) :=
  (Functor.Monoidal.commTensorLeft (sheafification α) ℱ).symm

end PresheafOfModules
