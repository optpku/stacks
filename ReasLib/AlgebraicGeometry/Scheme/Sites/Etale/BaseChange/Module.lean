/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (Λ : Type u) [Ring Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]

/-- The underived Sites pullback mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of a cartesian
square, obtained as the right mate of the inverse-image square. -/
def etaleModulePushforwardBaseChange :
    etaleModulePushforward f Λ ⋙ Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⟶
      Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ) ⋙ etaleModulePushforward f' Λ :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback f').sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      Y'.smallEtaleTopology X'.smallEtaleTopology)
    (etaleModuleSheafPullback_square f g f' g' h_cart Λ)

/-- The underived mate is the right mate of the inverse-image square. -/
theorem etaleModulePushforwardBaseChange_eq :
    etaleModulePushforwardBaseChange f g f' g' h_cart Λ =
      DerivedBaseChange.map
        ((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology)
        ((smallEtalePullback f').sheafAdjunctionContinuous (ModuleCat.{u} Λ)
          Y'.smallEtaleTopology X'.smallEtaleTopology)
        (etaleModuleSheafPullback_square f g f' g' h_cart Λ) :=
  sorry

variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

section CompactSupportBaseChange

variable [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [LocallyQuasiFinite f']
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]

/-- Forgetting coefficients identifies `g⁻¹ (f_! F)` with
`g⁻¹ ((etaleLowerShriek f) (forget F))` along `lowerShriekModule_forget`
and `lowerShriekIso_separated`. -/
def lowerShriekModuleBaseChange_forgetLeft
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)) ≅
      (etaleAbelianSheafPullback g).obj
        ((etaleLowerShriek f).obj (etaleModuleForget Λ F)) :=
  (etaleModuleSheafPullback_compSheafComposeIso g Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (etaleAbelianSheafPullback g).mapIso
      ((lowerShriekModule_forgetFunctorIso f Λ).app F ≪≫
        (lowerShriekIso_separated f).app (etaleModuleForget Λ F))

/-- Forgetting coefficients identifies `f'_! ((g')⁻¹ F)` with
`(etaleLowerShriek f') ((g')⁻¹ (forget F))`. -/
def lowerShriekModuleBaseChange_forgetRight
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)) ≅
      (etaleLowerShriek f').obj
        ((etaleAbelianSheafPullback g').obj (etaleModuleForget Λ F)) :=
  (lowerShriekModule_forgetFunctorIso f' Λ).app
      ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F) ≪≫
    (lowerShriekIso_separated f').app
      (etaleModuleForget Λ ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)) ≪≫
    (etaleLowerShriek f').mapIso
      ((etaleModuleSheafPullback_compSheafComposeIso g' Λ).app F)

/-- The compact-support base-change map on underlying abelian sheaves respects scalar multiplication. -/
theorem lowerShriekModuleBaseChange_smul
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : Y'.Etaleᵒᵖ) (r : Λ)
    (x : ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)).obj.obj U) :
    (((lowerShriekModuleBaseChange_forgetLeft f g Λ F).hom ≫
          etaleLowerShriekBaseChange_app f g f' g' h_cart (etaleModuleForget Λ F) ≫
          (lowerShriekModuleBaseChange_forgetRight f' g' Λ F).inv).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ)
        (β := ((lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)).obj.obj U)
        (γ := ((lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)).obj.obj U)
        r ((((lowerShriekModuleBaseChange_forgetLeft f g Λ F).hom ≫
          etaleLowerShriekBaseChange_app f g f' g' h_cart (etaleModuleForget Λ F) ≫
          (lowerShriekModuleBaseChange_forgetRight f' g' Λ F).inv).hom.app U).hom x) := sorry

/-- The compact-support base-change morphism of module sheaves is the scalar-compatible lift of the abelian comparison. -/
def lowerShriekModuleBaseChange_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F) ⟶
      (lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F) :=
  liftModuleSheafHom
    ((lowerShriekModuleBaseChange_forgetLeft f g Λ F).hom ≫
          etaleLowerShriekBaseChange_app f g f' g' h_cart (etaleModuleForget Λ F) ≫
          (lowerShriekModuleBaseChange_forgetRight f' g' Λ F).inv)
    (lowerShriekModuleBaseChange_smul f g f' g' h_cart Λ F)

/-- Compact-support base change is natural in the module sheaf. -/
theorem lowerShriekModuleBaseChange_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)} (α : F ⟶ G) :
    (lowerShriekModule f Λ ⋙ Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).map α ≫
        lowerShriekModuleBaseChange_app f g f' g' h_cart Λ G =
      lowerShriekModuleBaseChange_app f g f' g' h_cart Λ F ≫
        (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ) ⋙ lowerShriekModule f' Λ).map α := sorry

/-- The canonical compact-support base-change transformation on étale module sheaves. -/
def lowerShriekModuleBaseChange :
    lowerShriekModule f Λ ⋙ Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⟶
      Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ) ⋙ lowerShriekModule f' Λ where
  app := lowerShriekModuleBaseChange_app f g f' g' h_cart Λ
  naturality := fun _ _ α ↦ lowerShriekModuleBaseChange_naturality f g f' g' h_cart Λ α

/-- The objectwise comparison is the component of
`lowerShriekModuleBaseChange`. -/
theorem lowerShriekModuleBaseChange_app_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    lowerShriekModuleBaseChange_app f g f' g' h_cart Λ F =
      (lowerShriekModuleBaseChange f g f' g' h_cart Λ).app F :=
  sorry

/-- After forgetting coefficients and identifying compact support with
`etaleLowerShriek`, the module comparison is the canonical abelian compact-support comparison. -/
theorem lowerShriekModuleBaseChange_eq_etaleLowerShriekBaseChange
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map
        (lowerShriekModuleBaseChange_app f g f' g' h_cart Λ F) =
      (lowerShriekModuleBaseChange_forgetLeft f g Λ F).hom ≫
        etaleLowerShriekBaseChange_app f g f' g' h_cart
          (etaleModuleForget Λ F) ≫
        (lowerShriekModuleBaseChange_forgetRight f' g' Λ F).inv :=
  sorry

/-- Derived compact-support base change `g⁻¹ f_! ⟶ f'_! (g')⁻¹` on
`D(X_étale, Λ)`, obtained by applying `mapDerivedCategory` to the underived
comparison. -/
@[irreducible]
def lowerShriekModuleDerivedBaseChange :
    lowerShriekModuleDerived f Λ ⋙ etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙ lowerShriekModuleDerived f' Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (lowerShriekModule f Λ)) (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))).inv ≫
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk
        (lowerShriekModuleBaseChange f g f' g' h_cart Λ) :
        ExactFunctor.of
            (lowerShriekModule f Λ ⋙ Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)) ⟶
          ExactFunctor.of
            (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ) ⋙ lowerShriekModule f' Λ)) ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ))) (ExactFunctor.of (lowerShriekModule f' Λ))).hom

/-- The derived compact-support comparison at an object of `D(X_étale, Λ)`. -/
@[irreducible]
def lowerShriekModuleDerivedBaseChange_app (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage g Λ).obj
      ((lowerShriekModuleDerived f Λ).obj K) ⟶
      (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage g' Λ).obj K) :=
  (lowerShriekModuleDerivedBaseChange f g f' g' h_cart Λ).app K

/-- The derived lower-shriek base-change component is evaluation of the canonical transformation. -/
theorem lowerShriekModuleDerivedBaseChange_app_eq
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    lowerShriekModuleDerivedBaseChange_app f g f' g' h_cart Λ K =
      (lowerShriekModuleDerivedBaseChange f g f' g' h_cart Λ).app K := by
  unfold lowerShriekModuleDerivedBaseChange_app
  rfl

end CompactSupportBaseChange

/-- The iterated cochain unit for `Rf_* ⋙ g⁻¹`, using exactness of inverse
image. -/
def etaleDerivedPushforwardBaseChange_srcUnit
    [(etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)) ⟶
      DerivedCategory.Q ⋙
        (etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ) :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePushforward f Λ ⋙ Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))
        (ComplexShape.up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    (Functor.associator ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ)) ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    whiskerLeft
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.inv ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleModuleDerivedInverseImage g Λ)).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleModulePushforward f Λ))
      (etaleModuleDerivedInverseImage g Λ) ≫
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedPushforward f)
      (etaleModuleDerivedInverseImage g Λ)).hom

/-- Exactness of inverse image makes `Rf_* ⋙ g⁻¹` a right-derived functor of
`f_* ⋙ g⁻¹`. -/
instance etaleDerivedPushforwardBaseChange_src_isRightDerived
    [(etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (etaleDerivedPushforward f ⋙
        etaleModuleDerivedInverseImage g Λ).IsRightDerivedFunctor
      (etaleDerivedPushforwardBaseChange_srcUnit f g Λ)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  sorry

/-- The iterated cochain unit for `(g')⁻¹ ⋙ Rf'_*`. -/
def etaleDerivedPushforwardBaseChange_tgtUnit
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ) ⋙ etaleModulePushforward f' Λ) ⟶
      DerivedCategory.Q ⋙
        (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f') :=
  RightDerived.Cochain.ExactFirst.unit
    (ExactFunctor.of (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)))
    (etaleModulePushforward f' Λ)

/-- Derived base-change mate `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of a cartesian square,
on unbounded derived categories of étale module sheaves. -/
@[irreducible]
def etaleDerivedPushforwardBaseChange
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f' :=
  rightDerivedNatTrans
    (etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ)
    (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f')
    (etaleDerivedPushforwardBaseChange_srcUnit f g Λ)
    (etaleDerivedPushforwardBaseChange_tgtUnit f' g' Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (whiskerRight
      (NatTrans.mapHomologicalComplex
        (etaleModulePushforwardBaseChange f g f' g' h_cart Λ)
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))))

/-- The derived `Rf_*` base-change comparison at an object of `D(X_étale, Λ)`. -/
@[irreducible]
def etaleDerivedPushforwardBaseChange_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage g Λ).obj
      ((etaleDerivedPushforward f).obj K) ⟶
      (etaleDerivedPushforward f').obj
        ((etaleModuleDerivedInverseImage g' Λ).obj K) :=
  (etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ).app K

/-- The derived pushforward base-change component is evaluation of the canonical mate. -/
theorem etaleDerivedPushforwardBaseChange_app_eq
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedPushforwardBaseChange_app f g f' g' h_cart Λ K =
      (etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ).app K := by
  unfold etaleDerivedPushforwardBaseChange_app
  rfl

/-- The derived `Rf_*` mate is the right-derived natural transformation of the
underived Sites mate. -/
theorem etaleDerivedPushforwardBaseChange_eq
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ =
      rightDerivedNatTrans
        (etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage g Λ)
        (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f')
        (etaleDerivedPushforwardBaseChange_srcUnit f g Λ)
        (etaleDerivedPushforwardBaseChange_tgtUnit f' g' Λ)
        (HomologicalComplex.quasiIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
        (whiskerRight
          (NatTrans.mapHomologicalComplex
            (etaleModulePushforwardBaseChange f g f' g' h_cart Λ)
            (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
              DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
