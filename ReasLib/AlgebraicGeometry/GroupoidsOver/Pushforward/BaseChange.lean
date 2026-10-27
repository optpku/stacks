/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InverseImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.HigherDirectImage
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits
open CategoryTheory.Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Pushforward

variable {S : Scheme.{u}}
variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) (τ : StandardTopology)

/-- Continuous-cocontinuous adjunction `f⁻¹ ⊣ f_*` on associated abelian `τ`-sheaves. -/
abbrev abelianInverseImageAdjunction :
    associatedAbelianInverseImage f τ ⊣ abelianPushforward f τ :=
  (toCartesianBasedFunctor f).toFunctor.sheafAdjunctionCocontinuous
    AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)

/-- The canonical underived comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian sheaves,
the mate of `abelianInverseImage_twoFibreIso`. -/
def abelianBaseChangeHom :
    abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ ⟶
      associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ :=
  CategoryTheory.DerivedBaseChange.map
    (abelianInverseImageAdjunction f τ)
    (abelianInverseImageAdjunction (fibreProductFst f g) τ)
    (abelianInverseImage_twoFibreIso f τ g)

/-- The underived abelian comparison is invertible. -/
instance abelianBaseChangeHom_isIso :
    IsIso (abelianBaseChangeHom f g τ) :=
  sorry


/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of abelian sheaves on
the chosen 2-fibre product. -/
def abelianBaseChangeIso :
    abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ ≅
      associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ :=
  asIso (abelianBaseChangeHom f g τ)

/-- `abelianBaseChangeIso` has forward map the mate of the inverse-image 2-cell. -/
theorem abelianBaseChangeIso_hom :
    (abelianBaseChangeIso f g τ).hom =
      abelianBaseChangeHom f g τ :=
  rfl

/-- Component of the underived abelian base-change isomorphism at a sheaf `F`. -/
def abelianBaseChangeIso_app
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    (associatedAbelianInverseImage g τ).obj ((abelianPushforward f τ).obj F) ≅
      (abelianPushforward (fibreProductFst f g) τ).obj
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).obj F) :=
  (abelianBaseChangeIso f g τ).app F

variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1}]

/-- Forgetting module structure identifies the two underived module composites with the
abelian base-change isomorphism. -/
def moduleBaseChangeForgetIso
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (SheafOfModules.toSheaf (associatedStructureSheaf Y' τ)).obj
      ((associatedModuleInverseImage g τ).obj ((modulePushforward f τ).obj G)) ≅
      (SheafOfModules.toSheaf (associatedStructureSheaf Y' τ)).obj
        ((modulePushforward (fibreProductFst f g) τ).obj
          ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj G)) :=
  (associatedModuleInverseImage_underlyingIso g τ).app ((modulePushforward f τ).obj G) ≪≫
    (associatedAbelianInverseImage g τ).mapIso ((modulePushforward_toSheafIso f τ).app G) ≪≫
    (abelianBaseChangeIso f g τ).app
      ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) ≪≫
    ((abelianPushforward (fibreProductFst f g) τ).mapIso
        ((associatedModuleInverseImage_underlyingIso (fibreProductSnd f g) τ).app G)).symm ≪≫
      ((modulePushforward_toSheafIso (fibreProductFst f g) τ).app
          ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj G)).symm

/-- The canonical forgotten base-change map respects the structure-sheaf action. -/
theorem moduleBaseChangeHom_smul
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (y : Y'.totalᵒᵖ) (r : (associatedStructureSheaf Y' τ).obj.obj y)
    (m : ((associatedModuleInverseImage g τ).obj ((modulePushforward f τ).obj F)).val.obj y) :
    (moduleBaseChangeForgetIso f g τ F).hom.hom.app y (r • m) =
      ((((modulePushforward (fibreProductFst f g) τ).obj
          ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj F)).val.obj y).smul r).hom
        ((moduleBaseChangeForgetIso f g τ F).hom.hom.app y m) := sorry

/-- The component of module base change is the linear lift of its forgotten map. -/
def moduleBaseChangeHom_app
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (associatedModuleInverseImage g τ).obj ((modulePushforward f τ).obj F) ⟶
      (modulePushforward (fibreProductFst f g) τ).obj
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj F) where
  val := PresheafOfModules.homMk (moduleBaseChangeForgetIso f g τ F).hom.hom
    (moduleBaseChangeHom_smul f g τ F)

/-- Module base change is natural in the input module sheaf. -/
theorem moduleBaseChangeHom_naturality
    {F G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)} (α : F ⟶ G) :
    (modulePushforward f τ ⋙ associatedModuleInverseImage g τ).map α ≫
        moduleBaseChangeHom_app f g τ G =
      moduleBaseChangeHom_app f g τ F ≫
        (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
          modulePushforward (fibreProductFst f g) τ).map α := sorry

/-- The canonical module base-change transformation lifts the forgotten comparison. -/
def moduleBaseChangeHom :
    modulePushforward f τ ⋙ associatedModuleInverseImage g τ ⟶
      associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ where
  app := moduleBaseChangeHom_app f g τ
  naturality := fun _ _ α ↦ moduleBaseChangeHom_naturality f g τ α

/-- Forgetting the module comparison gives the specified additive comparison. -/
theorem moduleBaseChangeHom_toSheaf
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (SheafOfModules.toSheaf (associatedStructureSheaf Y' τ)).map
        ((moduleBaseChangeHom f g τ).app F) =
      (moduleBaseChangeForgetIso f g τ F).hom := rfl

/-- The canonical underived module base-change transformation is invertible. -/
instance moduleBaseChangeHom_isIso : IsIso (moduleBaseChangeHom f g τ) := sorry

/-- The canonical underived module base-change isomorphism. -/
def moduleBaseChangeIso :
    modulePushforward f τ ⋙ associatedModuleInverseImage g τ ≅
      associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ :=
  asIso (moduleBaseChangeHom f g τ)

/-- Component of the underived module base-change isomorphism at a sheaf of modules. -/
def moduleBaseChangeIso_app
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (associatedModuleInverseImage g τ).obj ((modulePushforward f τ).obj G) ≅
      (modulePushforward (fibreProductFst f g) τ).obj
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj G) :=
  (moduleBaseChangeIso f g τ).app G

end AlgebraicGeometry.GroupoidsOver.Pushforward
