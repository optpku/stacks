/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.AbelianInverseImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Adjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Composition
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-!
# Underived étale base change
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The inverse-image 2-cell of the chosen 2-fibre product on abelian étale
sheaves: `g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`. -/
def etaleAbelianInverseImage_twoFibreIso :
    etaleAbelianInverseImage g ⋙
        etaleAbelianInverseImage (fibreProductFst f g) ≅
      etaleAbelianInverseImage f ⋙
        etaleAbelianInverseImage (fibreProductSnd f g) :=
  (etaleAbelianInverseImage_compIso (fibreProductFst f g) g).symm ≪≫
    sheafPushforwardContinuousIso
        (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f))
        AddCommGrpCat.{u} (fibreProductApex f g).etaleTopology Y.etaleTopology ≪≫
      etaleAbelianInverseImage_compIso (fibreProductSnd f g) f

/-- `etaleAbelianInverseImage_twoFibreIso` is the composite of composition
comparisons with the 2-fibre-product 2-cell. -/
theorem etaleAbelianInverseImage_twoFibreIso_eq :
    etaleAbelianInverseImage_twoFibreIso f g =
      (etaleAbelianInverseImage_compIso (fibreProductFst f g) g).symm ≪≫
        sheafPushforwardContinuousIso
            (toFunctorIso
              (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f))
            AddCommGrpCat.{u} (fibreProductApex f g).etaleTopology
            Y.etaleTopology ≪≫
          etaleAbelianInverseImage_compIso (fibreProductSnd f g) f :=
  rfl

variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- The canonical underived comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian étale
sheaves, the mate of `etaleAbelianInverseImage_twoFibreIso`. -/
def etaleAbelianPushforwardBaseChangeHom :
    etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g ⟶
      etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g) :=
  CategoryTheory.DerivedBaseChange.map
    (etaleAbelianInverseImage_adjunction f)
    (etaleAbelianInverseImage_adjunction (fibreProductFst f g))
    (etaleAbelianInverseImage_twoFibreIso f g)

/-- The underived étale abelian comparison is invertible. -/
instance etaleAbelianPushforwardBaseChangeHom.isIso :
    IsIso (etaleAbelianPushforwardBaseChangeHom f g) :=
  sorry

/-- The reverse underived comparison `f'_* (g')⁻¹ ⟶ g⁻¹ f_*`. -/
def etaleAbelianPushforwardBaseChangeInv :
    etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g) ⟶
      etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g :=
  inv (etaleAbelianPushforwardBaseChangeHom f g)

/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of abelian étale
sheaves on the chosen 2-fibre product. -/
def etaleAbelianPushforwardBaseChangeIso :
    etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g ≅
      etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g) :=
  asIso (etaleAbelianPushforwardBaseChangeHom f g)

/-- `etaleAbelianPushforwardBaseChangeIso` has forward map the mate of the
inverse-image 2-cell. -/
theorem etaleAbelianPushforwardBaseChangeIso_eq :
    (etaleAbelianPushforwardBaseChangeIso f g).hom =
      etaleAbelianPushforwardBaseChangeHom f g :=
  rfl

/-- Component of the underived étale abelian base-change isomorphism at a sheaf. -/
def etaleAbelianPushforwardBaseChangeIso_app
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianInverseImage g).obj ((etaleAbelianPushforward f).obj ℱ) ≅
      (etaleAbelianPushforward (fibreProductFst f g)).obj
        ((etaleAbelianInverseImage (fibreProductSnd f g)).obj ℱ) :=
  (etaleAbelianPushforwardBaseChangeIso f g).app ℱ

/-- Inverse image of étale modules is additive. -/
instance etaleModuleInverseImage.instAdditive {A B : GroupoidsOver S} (h : A ⟶ B) :
    (etaleModuleInverseImage h).Additive :=
  sorry

/-- Inverse image of étale modules preserves homology. -/
instance etaleModuleInverseImage.instPreservesHomology {A B : GroupoidsOver S}
    (h : A ⟶ B) : (etaleModuleInverseImage h).PreservesHomology :=
  sorry

/-- Inverse image of étale modules preserves finite limits. -/
instance etaleModuleInverseImage.instPreservesFiniteLimits {A B : GroupoidsOver S}
    (h : A ⟶ B) : PreservesFiniteLimits (etaleModuleInverseImage h) :=
  sorry

/-- Inverse image of étale modules preserves finite colimits. -/
instance etaleModuleInverseImage.instPreservesFiniteColimits
    {A B : GroupoidsOver S} (h : A ⟶ B) :
    PreservesFiniteColimits (etaleModuleInverseImage h) :=
  sorry

variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- The inverse-image 2-cell of the chosen 2-fibre product on étale modules:
`g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`. -/
def etaleModuleInverseImage_twoFibreIso :
    etaleModuleInverseImage g ⋙ etaleModuleInverseImage (fibreProductFst f g) ≅
      etaleModuleInverseImage f ⋙ etaleModuleInverseImage (fibreProductSnd f g) :=
  etaleModuleInverseImage_comp (fibreProductFst f g) g ≪≫
    etaleModuleInverseImage_iso
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f) ≪≫
    (etaleModuleInverseImage_comp (fibreProductSnd f g) f).symm

/-- The canonical underived comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of étale modules,
the mate of `etaleModuleInverseImage_twoFibreIso`. -/
def etaleModulePushforwardBaseChangeHom :
    etaleModuleDirectImage f ⋙ etaleModuleInverseImage g ⟶
      etaleModuleInverseImage (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g) :=
  CategoryTheory.DerivedBaseChange.map
    (etaleModuleAdjunction f)
    (etaleModuleAdjunction (fibreProductFst f g))
    (etaleModuleInverseImage_twoFibreIso f g)

/-- The underived étale module comparison is invertible. -/
instance etaleModulePushforwardBaseChangeHom.isIso :
    IsIso (etaleModulePushforwardBaseChangeHom f g) :=
  sorry

/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of étale modules
on the chosen 2-fibre product. -/
def etaleModulePushforwardBaseChangeIso :
    etaleModuleDirectImage f ⋙ etaleModuleInverseImage g ≅
      etaleModuleInverseImage (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g) :=
  asIso (etaleModulePushforwardBaseChangeHom f g)

/-- Component of the underived étale module base-change isomorphism. -/
def etaleModulePushforwardBaseChangeIso_app
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (etaleModuleInverseImage g).obj ((etaleModuleDirectImage f).obj ℳ) ≅
      (etaleModuleDirectImage (fibreProductFst f g)).obj
        ((etaleModuleInverseImage (fibreProductSnd f g)).obj ℳ) :=
  (etaleModulePushforwardBaseChangeIso f g).app ℳ


end AlgebraicGeometry.GroupoidsOver
