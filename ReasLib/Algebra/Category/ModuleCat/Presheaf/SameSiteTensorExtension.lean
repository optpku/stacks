/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

@[expose] public section
open CategoryTheory
noncomputable section
universe c v w
namespace PresheafOfModules.SameSiteTensorExtension
variable {C : Type c} [Category.{v} C]
variable {R S : Cᵒᵖ ⥤ CommRingCat.{w}} (α : R ⟶ S)

abbrev ringMap : (R ⋙ forget₂ CommRingCat RingCat) ⟶
    (S ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

theorem square {U V : Cᵒᵖ} (i : U ⟶ V) :
    (α.app V).hom.comp (R.map i).hom = (S.map i).hom.comp (α.app U).hom :=
  congrArg CommRingCat.Hom.hom (α.naturality i)

def restriction (M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars (S.map i).hom).obj
        ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) :=
  let target := (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)
  ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm
    (M.map i ≫
      (ModuleCat.restrictScalars (R.map i).hom).map
        ((ModuleCat.extendRestrictScalarsAdj (α.app V).hom).unit.app (M.obj V)) ≫
      (ModuleCat.restrictScalarsComp'App (R.map i).hom (α.app V).hom
        ((α.app V).hom.comp (R.map i).hom) rfl target).inv ≫
      (eqToIso (congrArg (fun h : R.obj U →+* S.obj V ↦
        (ModuleCat.restrictScalars h).obj target) (square α i))).hom ≫
      (ModuleCat.restrictScalarsComp'App (α.app U).hom (S.map i).hom
        ((S.map i).hom.comp (α.app U).hom) rfl target).hom)

def obj (M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat) where
  obj U := (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)
  map i := restriction α M i
  map_id := sorry
  map_comp := sorry

def map {M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N) :
    obj α M ⟶ obj α N where
  app U := (ModuleCat.extendScalars (α.app U).hom).map (f.app U)
  naturality := sorry

def functor : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) ⥤
    PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat) where
  obj := obj α
  map := map α
  map_id := sorry
  map_comp := sorry

def homEquiv (M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) :
    (obj α M ⟶ N) ≃ (M ⟶ (PresheafOfModules.restrictScalars (ringMap α)).obj N) where
  toFun f :=
    { app U := (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _ (f.app U)
      naturality := sorry }
  invFun f :=
    { app U := ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm (f.app U)
      naturality := sorry }
  left_inv := sorry
  right_inv := sorry

def adjunction : functor α ⊣ PresheafOfModules.restrictScalars (ringMap α) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv α
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

end PresheafOfModules.SameSiteTensorExtension
