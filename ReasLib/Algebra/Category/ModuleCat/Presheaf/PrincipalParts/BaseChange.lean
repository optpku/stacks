/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.Truncation
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.BaseChange.Truncation

import all ReasLib.Algebra.Module.PrincipalParts.Basic
import all ReasLib.Algebra.Module.PrincipalParts.RingHom

/-!
# Base change for principal-parts presheaves

A commutative square of commutative-ring presheaves and a compatible morphism of module
presheaves induce the sectionwise base-change map on principal parts.  The sectionwise maps
assemble into a morphism of presheaves and commute with order truncation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts.BaseChange

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ O₁' O₂' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {β : O₂ ⟶ O₂'}
variable (sq : CommSq a φ φ' β)
variable {F : PresheafOfModules (ringPresheaf O₂)}
variable {F' : PresheafOfModules (ringPresheaf O₂')}
variable (α : F ⟶
  (PresheafOfModules.restrictScalars
    (PresheafOfModules.presheafStructureMap β)).obj F')

private theorem hom_ext_universalClass (k : ℕ) (X : Cᵒᵖ)
    {N : ModuleCat (O₂.obj X)}
    {f g : PresheafOfModules.PrincipalParts.module φ F k X ⟶ N}
    (h : ∀ m : F.obj X,
      f.hom (PresheafOfModules.PrincipalParts.universalClass φ F k X m) =
        g.hom (PresheafOfModules.PrincipalParts.universalClass φ F k X m)) : f = g := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  letI : Module (O₁.obj X) N :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom N
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) N := IsScalarTower.of_compHom _ _ _
  apply ModuleCat.hom_ext
  exact _root_.PrincipalParts.linearMap_ext k h

include sq in
/-- A commutative square of ring presheaves commutes after evaluation at every site object. -/
theorem comm_app (X : Cᵒᵖ) :
    (β.app X).hom.comp (φ.app X).hom =
      (φ'.app X).hom.comp (a.app X).hom := by
  exact (congrArg (fun p : O₁ ⟶ O₂' => (p.app X).hom) sq.w).symm

/-- The sectionwise principal-parts map induced by a commutative square of ring presheaves and
a compatible morphism of module presheaves. -/
noncomputable def mapApp (k : ℕ) (X : Cᵒᵖ) :
    PresheafOfModules.PrincipalParts.module φ F k X ⟶
      (ModuleCat.restrictScalars (β.app X).hom).obj
        (PresheafOfModules.PrincipalParts.module φ' F' k X) :=
  _root_.PrincipalParts.RingHom.BaseChange.map
    (φ.app X).hom (φ'.app X).hom (a.app X).hom (β.app X).hom
      (comm_app sq X) k (α.app X)

/-- The sectionwise base-change map sends each universal class to the universal class of the
image section. -/
@[simp]
theorem mapApp_universalClass (k : ℕ) (X : Cᵒᵖ) (m : F.obj X) :
    (mapApp sq α k X).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F k X m) =
      PresheafOfModules.PrincipalParts.universalClass φ' F' k X ((α.app X).hom m) := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  unfold mapApp _root_.PrincipalParts.RingHom.BaseChange.map
    _root_.PrincipalParts.BaseChange.moduleMap
  unfold _root_.PrincipalParts.BaseChange.Internal.mapFun _root_.PrincipalParts.BaseChange.map
  erw [_root_.PrincipalParts.representingEquiv_symm_apply_universalDifferential]
  rfl

/-- The sectionwise base-change maps commute with restriction along morphisms of the site. -/
theorem mapApp_naturality (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    PresheafOfModules.PrincipalParts.restrictionMap φ F k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (mapApp sq α k Y) =
      mapApp sq α k X ≫
        ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap β)).obj
          (PresheafOfModules.PrincipalParts.presheaf φ' F' k)).map f := by
  apply hom_ext_universalClass (φ := φ) (F := F) k X
  intro m
  change (mapApp sq α k Y).hom
      ((PresheafOfModules.PrincipalParts.restrictionMap φ F k f).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F k X m)) =
    (PresheafOfModules.PrincipalParts.restrictionMap φ' F' k f).hom
      ((mapApp sq α k X).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F k X m))
  rw [PresheafOfModules.PrincipalParts.restrictionMap_universalClass,
    mapApp_universalClass, mapApp_universalClass,
    PresheafOfModules.PrincipalParts.restrictionMap_universalClass]
  congr 1
  exact PresheafOfModules.naturality_apply α f m

/-- Tag 0G3W: base change for principal parts as a morphism of module presheaves. -/
@[stacks 0G3W "presheaf principal-parts base change"]
noncomputable def map (k : ℕ) :
    PresheafOfModules.PrincipalParts.presheaf φ F k ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap β)).obj
        (PresheafOfModules.PrincipalParts.presheaf φ' F' k) where
  app X := mapApp sq α k X
  naturality f := mapApp_naturality sq α k f

section Identity

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The identity ring-presheaf square commutes. -/
theorem idSquare (φ : O₁ ⟶ O₂) : CommSq (𝟙 O₁) φ φ (𝟙 O₂) := by
  constructor
  simp

/-- Principal-parts base change along the identity square is the canonical identity-restriction
morphism. -/
@[simp]
theorem map_id (φ : O₁ ⟶ O₂) (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    map (idSquare φ)
        ((Restriction.idIso (ringPresheaf O₂)).hom.app F) k =
      (Restriction.idIso (ringPresheaf O₂)).hom.app
        (PresheafOfModules.PrincipalParts.presheaf φ F k) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply hom_ext_universalClass (φ := φ) (F := F) k X
  intro m
  change (mapApp (idSquare φ) ((Restriction.idIso (ringPresheaf O₂)).hom.app F) k X).hom
      (PresheafOfModules.PrincipalParts.universalClass φ F k X m) =
    PresheafOfModules.PrincipalParts.universalClass φ F k X m
  exact mapApp_universalClass (idSquare φ)
    ((Restriction.idIso (ringPresheaf O₂)).hom.app F) k X m

end Identity

section Composition

variable {O₂ O₂' O₂'' : Cᵒᵖ ⥤ CommRingCat.{max u v}}

variable {O₁ O₁' O₁'' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {β : O₂ ⟶ O₂'}
variable {a' : O₁' ⟶ O₁''} {φ'' : O₁'' ⟶ O₂''} {β' : O₂' ⟶ O₂''}

/-- Principal-parts base-change morphisms preserve composition of ring squares and compatible
module-presheaf morphisms, with scalar restrictions identified by `Restriction.compIso`. -/
@[simp]
theorem map_comp
    (sq : CommSq a φ φ' β) (sq' : CommSq a' φ' φ'' β')
    {F : PresheafOfModules (ringPresheaf O₂)}
    {F' : PresheafOfModules (ringPresheaf O₂')}
    {F'' : PresheafOfModules (ringPresheaf O₂'')}
    (α : F ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap β)).obj F')
    (α' : F' ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap β')).obj F'')
    (k : ℕ) :
    map sq α k ≫
        (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap β)).map
          (map sq' α' k) ≫
        (Restriction.compIso
          (PresheafOfModules.presheafStructureMap β)
          (PresheafOfModules.presheafStructureMap β')).hom.app
            (PresheafOfModules.PrincipalParts.presheaf φ'' F'' k) =
      map (CommSq.horiz_comp sq sq')
        (Restriction.homComp
          (PresheafOfModules.presheafStructureMap β)
          (PresheafOfModules.presheafStructureMap β') α α') k := by
  apply PresheafOfModules.hom_ext
  intro X
  apply hom_ext_universalClass (φ := φ) (F := F) k X
  intro m
  change (mapApp sq' α' k X).hom
      ((mapApp sq α k X).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F k X m)) =
    (mapApp (CommSq.horiz_comp sq sq')
      (Restriction.homComp
        (PresheafOfModules.presheafStructureMap β)
        (PresheafOfModules.presheafStructureMap β') α α') k X).hom
      (PresheafOfModules.PrincipalParts.universalClass φ F k X m)
  rw [mapApp_universalClass, mapApp_universalClass, mapApp_universalClass]
  rfl

end Composition

private theorem truncateApp_universalClass_eq {k l : ℕ} (h : k ≤ l)
    (X : Cᵒᵖ) (m : F.obj X) :
    (PresheafOfModules.PrincipalParts.truncateApp φ F h X).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F l X m) =
      PresheafOfModules.PrincipalParts.universalClass φ F k X m := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  unfold PresheafOfModules.PrincipalParts.truncateApp
    _root_.PrincipalParts.RingHom.truncate _root_.PrincipalParts.truncate
  erw [_root_.PrincipalParts.representingEquiv_symm_apply_universalDifferential]

/-- Sectionwise base change commutes with truncation of the order bound. -/
theorem mapApp_truncate {k l : ℕ} (h : k ≤ l) (X : Cᵒᵖ) :
    mapApp sq α l X ≫
        (ModuleCat.restrictScalars (β.app X).hom).map
          (PresheafOfModules.PrincipalParts.truncateApp φ' F' h X) =
      PresheafOfModules.PrincipalParts.truncateApp φ F h X ≫
        mapApp sq α k X := by
  apply hom_ext_universalClass (φ := φ) (F := F) l X
  intro m
  change (PresheafOfModules.PrincipalParts.truncateApp φ' F' h X).hom
      ((mapApp sq α l X).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F l X m)) =
    (mapApp sq α k X).hom
      ((PresheafOfModules.PrincipalParts.truncateApp φ F h X).hom
        (PresheafOfModules.PrincipalParts.universalClass φ F l X m))
  rw [mapApp_universalClass, truncateApp_universalClass_eq,
    truncateApp_universalClass_eq, mapApp_universalClass]

/-- Base change of principal-parts presheaves commutes with truncation of the order bound. -/
theorem map_truncate {k l : ℕ} (h : k ≤ l) :
    map sq α l ≫
        (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap β)).map
          (PresheafOfModules.PrincipalParts.truncate φ' F' h) =
      PresheafOfModules.PrincipalParts.truncate φ F h ≫
        map sq α k := by
  apply PresheafOfModules.hom_ext
  intro X
  exact mapApp_truncate sq α h X

end PresheafOfModules.PrincipalParts.BaseChange
