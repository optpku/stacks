/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.Module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

variable {A B : CosimplicialObject CommRingCat.{u}}

/-- The morphism of commutative-ring presheaves induced by a cosimplicial ring morphism. -/
abbrev commRingMap (f : A ⟶ B) : cosimplicialCommRing A ⟶ cosimplicialCommRing B :=
  Functor.whiskerLeft (unopUnop SimplexCategory) f

/-- The components of the induced ring-presheaf morphism are the original ring maps. -/
theorem commRingMap_app (f : A ⟶ B) (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (commRingMap f).app X = f.app (unop (unop X)) :=
  rfl

/-- A cosimplicial ring morphism commutes with the underlying ring structure maps. -/
theorem commRingMap_naturality (f : A ⟶ B)
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    ((commRingMap f).app Y).hom.comp ((moduleRingPresheaf A).map g).hom =
      ((moduleRingPresheaf B).map g).hom.comp ((commRingMap f).app X).hom := sorry

namespace CosimplicialModule

/-- The scalar-extension structure map obtained by extending the source degree and
restricting the target degree along the cosimplicial ring maps. -/
def extensionStructureMap (f : A ⟶ B)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A))
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (ModuleCat.extendScalars ((commRingMap f).app X).hom).obj (K.obj X) ⟶
      (ModuleCat.restrictScalars ((moduleRingPresheaf B).map g).hom).obj
        ((ModuleCat.extendScalars ((commRingMap f).app Y).hom).obj (K.obj Y)) :=
  let α := commRingMap f
  let extendedTarget := (ModuleCat.extendScalars (α.app Y).hom).obj (K.obj Y)
  let target := (ModuleCat.restrictScalars ((moduleRingPresheaf B).map g).hom).obj extendedTarget
  let generator : K.obj X ⟶ (ModuleCat.restrictScalars (α.app X).hom).obj target :=
    K.map g ≫
      (ModuleCat.restrictScalars ((moduleRingPresheaf A).map g).hom).map
        ((ModuleCat.extendRestrictScalarsAdj (α.app Y).hom).unit.app (K.obj Y)) ≫
      (ModuleCat.restrictScalarsComp'App ((moduleRingPresheaf A).map g).hom (α.app Y).hom
        ((α.app Y).hom.comp ((moduleRingPresheaf A).map g).hom) rfl extendedTarget).inv ≫
      (eqToIso (congrArg
        (fun h : (moduleRingPresheaf A).obj X →+* (moduleRingPresheaf B).obj Y ↦
          (ModuleCat.restrictScalars h).obj extendedTarget)
        (commRingMap_naturality f g))).hom ≫
      (ModuleCat.restrictScalarsComp'App (α.app X).hom ((moduleRingPresheaf B).map g).hom
        (((moduleRingPresheaf B).map g).hom.comp (α.app X).hom) rfl extendedTarget).hom
  ((ModuleCat.extendRestrictScalarsAdj (α.app X).hom).homEquiv _ _).symm generator

/-- Scalar-extension structure maps preserve identities through the scalar-restriction comparison. -/
private theorem extensionStructureMap_id (f : A ⟶ B)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A)) (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    extensionStructureMap f K (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((moduleRingPresheaf B).map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((moduleRingPresheaf B).map_id X))).inv.app _ := sorry

/-- Scalar-extension structure maps preserve composition through the scalar-restriction comparison. -/
private theorem extensionStructureMap_comp (f : A ⟶ B)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A))
    {X Y Z : (SimplexCategoryᵒᵖ)ᵒᵖ} (first : X ⟶ Y) (second : Y ⟶ Z) :
    extensionStructureMap f K (first ≫ second) =
      extensionStructureMap f K first ≫
        (ModuleCat.restrictScalars ((moduleRingPresheaf B).map first).hom).map
          (extensionStructureMap f K second) ≫
        (ModuleCat.restrictScalarsComp' ((moduleRingPresheaf B).map first).hom
          ((moduleRingPresheaf B).map second).hom ((moduleRingPresheaf B).map (first ≫ second)).hom
          (congrArg RingCat.Hom.hom ((moduleRingPresheaf B).map_comp first second))).inv.app _ := sorry

end CosimplicialModule

/-- Degreewise scalar extension of a module over a cosimplicial ring. -/
def extendScalarsObj (f : A ⟶ B) (K : PresheafOfModules.{u} (moduleRingPresheaf A)) :
    PresheafOfModules.{u} (moduleRingPresheaf B) where
  obj X := (ModuleCat.extendScalars ((commRingMap f).app X).hom).obj (K.obj X)
  map g := CosimplicialModule.extensionStructureMap f K g
  map_id X := by exact CosimplicialModule.extensionStructureMap_id f K X
  map_comp first second := by exact CosimplicialModule.extensionStructureMap_comp f K first second

namespace CosimplicialModule

/-- Degreewise extension of a module morphism commutes with scalar-extension structure maps. -/
private theorem extensionHom_naturality (f : A ⟶ B)
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ : K ⟶ M)
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (extendScalarsObj f K).map g ≫
        (ModuleCat.restrictScalars ((moduleRingPresheaf B).map g).hom).map
          ((ModuleCat.extendScalars ((commRingMap f).app Y).hom).map (φ.app Y)) =
      (ModuleCat.extendScalars ((commRingMap f).app X).hom).map (φ.app X) ≫
        (extendScalarsObj f M).map g := sorry

end CosimplicialModule

/-- Degreewise scalar extension of a morphism of cosimplicial modules. -/
def extendScalarsHom (f : A ⟶ B)
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ : K ⟶ M) :
    extendScalarsObj f K ⟶ extendScalarsObj f M where
  app X := (ModuleCat.extendScalars ((commRingMap f).app X).hom).map (φ.app X)
  naturality g := by exact CosimplicialModule.extensionHom_naturality f φ g

/-- The components of scalar extension are the ordinary scalar-extension maps. -/
theorem extendScalarsHom_app (f : A ⟶ B)
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ : K ⟶ M)
    (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (extendScalarsHom f φ).app X =
      (ModuleCat.extendScalars ((commRingMap f).app X).hom).map (φ.app X) :=
  rfl
