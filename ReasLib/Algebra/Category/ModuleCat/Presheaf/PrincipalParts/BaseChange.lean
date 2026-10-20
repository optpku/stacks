/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.Truncation
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.BaseChange.Truncation

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

include sq in
/-- A commutative square of ring presheaves commutes after evaluation at every site object. -/
theorem comm_app (X : Cᵒᵖ) :
    (β.app X).hom.comp (φ.app X).hom =
      (φ'.app X).hom.comp (a.app X).hom := sorry

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
      PresheafOfModules.PrincipalParts.universalClass φ' F' k X ((α.app X).hom m) := sorry

/-- The sectionwise base-change maps commute with restriction along morphisms of the site. -/
theorem mapApp_naturality (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    PresheafOfModules.PrincipalParts.restrictionMap φ F k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (mapApp sq α k Y) =
      mapApp sq α k X ≫
        ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap β)).obj
          (PresheafOfModules.PrincipalParts.presheaf φ' F' k)).map f := sorry

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
theorem idSquare (φ : O₁ ⟶ O₂) : CommSq (𝟙 O₁) φ φ (𝟙 O₂) := sorry

/-- Principal-parts base change along the identity square is the canonical identity-restriction
morphism. -/
@[simp]
theorem map_id (φ : O₁ ⟶ O₂) (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    map (idSquare φ)
        ((Restriction.idIso (ringPresheaf O₂)).hom.app F) k =
      (Restriction.idIso (ringPresheaf O₂)).hom.app
        (PresheafOfModules.PrincipalParts.presheaf φ F k) := sorry

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
          (PresheafOfModules.presheafStructureMap β') α α') k := sorry

end Composition

/-- Sectionwise base change commutes with truncation of the order bound. -/
theorem mapApp_truncate {k l : ℕ} (h : k ≤ l) (X : Cᵒᵖ) :
    mapApp sq α l X ≫
        (ModuleCat.restrictScalars (β.app X).hom).map
          (PresheafOfModules.PrincipalParts.truncateApp φ' F' h X) =
      PresheafOfModules.PrincipalParts.truncateApp φ F h X ≫
        mapApp sq α k X := sorry

/-- Base change of principal-parts presheaves commutes with truncation of the order bound. -/
theorem map_truncate {k l : ℕ} (h : k ≤ l) :
    map sq α l ≫
        (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap β)).map
          (PresheafOfModules.PrincipalParts.truncate φ' F' h) =
      PresheafOfModules.PrincipalParts.truncate φ F h ≫
        map sq α k := sorry

end PresheafOfModules.PrincipalParts.BaseChange
