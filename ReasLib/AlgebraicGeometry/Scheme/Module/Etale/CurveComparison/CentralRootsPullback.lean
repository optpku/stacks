/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsModuleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.EtaleRootsPullback

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace CentralRootsPullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n),
  (smallEtalePullback f).op.HasLeftKanExtension F]

/-- The transpose of the actual units/Kummer-kernel pullback map. -/
def additivePushMap :=
  ((smallEtalePullback_sheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _)
    (ActualEtaleRootsPullback.rootsOfUnityAddSheafPullbackHom f n)

/-- Rebundle its same section functions over the canonical central ring Z/n.
Every additive map between these canonical Z/n modules is Z/n-linear. -/
def pushMap : ActualRootsModule.liftedSheaf Y n ⟶
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))
      Y.smallEtaleTopology X.smallEtaleTopology).obj (ActualRootsModule.liftedSheaf X n) :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := ((additivePushMap f n).hom.app U).hom
          map_add' := ((additivePushMap f n).hom.app U).hom.map_add
          map_smul' := by sorry }
      naturality := by sorry }

/-- The actual central-linear geometric roots pullback, by the module-sheaf adjunction. -/
def map :
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))
      Y.smallEtaleTopology X.smallEtaleTopology).obj (ActualRootsModule.liftedSheaf Y n) ⟶
    ActualRootsModule.liftedSheaf X n :=
  ((smallEtalePullback_sheafAdjunction f
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))).homEquiv _ _).symm (pushMap f n)

variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)) AddCommGrpCat.{u + 1})]

/-- Forgetting the canonical central action leaves precisely the same roots sections. -/
def forgetIso :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)) AddCommGrpCat.{u + 1})).obj
        (ActualRootsModule.liftedSheaf X n) ≅ ActualRootsModule.additiveSheaf X n :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by sorry))

end CentralRootsPullback
