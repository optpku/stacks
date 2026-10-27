/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.Homotopy
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

@[expose] public section

open CategoryTheory
open Functor

noncomputable section

universe u v w g

namespace RingedSite.ToposHom.NativeDerived

/-- Additive global sections are morphisms from the structure module, with native addition. -/
def globalSections (X : RingedSite.{u, v, w}) :
    ModuleCat.{w} X ⥤ AddCommGrpCat.{max u w} :=
  @preadditiveCoyoneda _ _ (SheafOfModules.instPreadditive X.structureSheaf) |>.obj
    (Opposite.op (SheafOfModules.unit X.structureSheaf))

/-- Global sections preserve addition of module-sheaf morphisms. -/
instance globalSections_additive (X : RingedSite.{u, v, w}) :
    (globalSections X).Additive := by
  dsimp [globalSections]
  infer_instance

/-- Unbounded derived global sections are computed by the canonical K-injective model. -/
def derivedGlobalSections (X : RingedSite.{u, v, w})
    [a : Abelian (ModuleCat.{w} X)] [h : IsGrothendieckAbelian.{g} (ModuleCat.{w} X)] :
    RingedSite.NativeDerived.category.{w} X ⥤ DerivedCategory AddCommGrpCat.{max u w} := by
  have hNative : @IsGrothendieckAbelian.{g} (ModuleCat.{w} X) _
      (RingedSite.NativeDerived.abelian.{w} X) :=
    (Abelian.structure_eq a (RingedSite.NativeDerived.abelian.{w} X)) ▸ h
  -- Local instance justification (defeq pin): the K-injective model uses native module addition and the existing native abelian certificate.
  letI := RingedSite.NativeDerived.abelian.{w} X
  -- Local instance justification (defeq pin): the K-injective model must use the standard native module localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{w} X
  -- Local instance justification (defeq pin): transport the given Grothendieck certificate along uniqueness of abelian structures, without changing its size.
  letI := hNative
  exact KInjectiveModel.derived.{g} (globalSections X)

variable {X Y : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)

/-- Global sections of a module direct image identify canonically with sections on the source. -/
def globalSectionsPushforwardIso :
    f.modulePushforward ⋙ globalSections Y ≅ globalSections X := by
  let e (M : ModuleCat.{w} X) :
      (globalSections Y).obj (f.modulePushforward.obj M) ≃ (globalSections X).obj M :=
    (SheafOfModules.unitHomEquiv (f.modulePushforward.obj M)).trans
      ((Sheaf.InternalModule.ToInternal.sectionsEquiv Y.structureSheaf
        (f.modulePushforward.obj M)).symm.trans
        ((f.modulePushforwardSectionsEquiv M).trans
          ((Sheaf.InternalModule.ToInternal.sectionsEquiv X.structureSheaf M).trans
            (SheafOfModules.unitHomEquiv M).symm)))
  refine NatIso.ofComponents (fun M ↦
    { hom := AddCommGrpCat.ofHom
        { toFun := e M
          map_zero' := ?_
          map_add' := ?_ }
      inv := AddCommGrpCat.ofHom
        { toFun := (e M).symm
          map_zero' := ?_
          map_add' := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  all_goals sorry

variable [aX : Abelian (ModuleCat.{w} X)] [aY : Abelian (ModuleCat.{w} Y)]
variable [hX : IsGrothendieckAbelian.{g} (ModuleCat.{w} X)]
  [hY : IsGrothendieckAbelian.{g} (ModuleCat.{w} Y)]
variable [HasPushforward f]

/-- The canonical universal comparison from source derived sections to iterated derived direct image and sections. -/
def rGammaToPushforwardComparison :
    derivedGlobalSections X ⟶ pushforward f ⋙ derivedGlobalSections Y := by
  have hNativeX : @IsGrothendieckAbelian.{g} (ModuleCat.{w} X) _
      (RingedSite.NativeDerived.abelian.{w} X) :=
    (Abelian.structure_eq aX (RingedSite.NativeDerived.abelian.{w} X)) ▸ hX
  have hNativeY : @IsGrothendieckAbelian.{g} (ModuleCat.{w} Y) _
      (RingedSite.NativeDerived.abelian.{w} Y) :=
    (Abelian.structure_eq aY (RingedSite.NativeDerived.abelian.{w} Y)) ▸ hY
  -- Local instance justification (defeq pin): the extension and its units share native source module addition.
  letI := RingedSite.NativeDerived.abelian.{w} X
  -- Local instance justification (defeq pin): the extension and its units share native target module addition.
  letI := RingedSite.NativeDerived.abelian.{w} Y
  -- Local instance justification (defeq pin): retain the existing native source localization in the universal extension.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{w} X
  -- Local instance justification (defeq pin): retain the existing native target localization in the iterated units.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{w} Y
  -- Local instance justification (defeq pin): transport the source Grothendieck certificate to its equal native abelian structure.
  letI := hNativeX
  -- Local instance justification (defeq pin): transport the target Grothendieck certificate to its equal native abelian structure.
  letI := hNativeY
  -- Local instance justification (defeq pin): degreewise direct image uses its canonical native additive certificate.
  letI := modulePushforward_additive f
  let P := f.modulePushforward.mapHomotopyCategory (ComplexShape.up ℤ)
  let G := derivedGlobalSections Y
  let R := pushforward f
  let L := RingedSite.NativeDerived.localization.{w} X
  let β : Homotopy.toDerived (globalSections X) ⟶ L ⋙ R ⋙ G :=
    (isoWhiskerRight
      (mapHomotopyCategoryCompIso (globalSectionsPushforwardIso f)
        (ComplexShape.up ℤ)) DerivedCategory.Qh).inv ≫
    (associator P ((globalSections Y).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    whiskerLeft P (KInjectiveModel.Homotopy.unit.{g} (globalSections Y)) ≫
    (associator P (RingedSite.NativeDerived.localization.{w} Y) G).inv ≫
    whiskerRight
      (totalRightDerivedUnit (pushforwardToDerived f) L
        (RingedSite.NativeDerived.quasiIso.{w} X)) G ≫
    (associator L R G).hom
  exact KInjectiveModel.Homotopy.extensionDesc.{g} (globalSections X) (R ⋙ G) β

/-- The canonical derived sections/direct-image comparison is invertible. -/
instance rGammaToPushforwardComparison_isIso :
    IsIso (rGammaToPushforwardComparison f) := sorry

/-- The Leray identification is the inverse of the canonical universal derived comparison. -/
def rGammaPushforwardIso :
    pushforward f ⋙ derivedGlobalSections Y ≅ derivedGlobalSections X :=
  (asIso (rGammaToPushforwardComparison f)).symm

end RingedSite.ToposHom.NativeDerived
