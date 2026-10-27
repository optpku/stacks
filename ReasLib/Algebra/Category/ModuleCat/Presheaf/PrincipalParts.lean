/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DifferentialOperator
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.BaseChange

import all ReasLib.Algebra.Module.PrincipalParts.Basic
import all ReasLib.Algebra.Module.PrincipalParts.RingHom

/-!
# Principal parts of a presheaf of modules

This file assembles the sectionwise principal-parts modules associated to a morphism of
commutative-ring presheaves into a presheaf of modules.  It is independent of a Grothendieck
topology; sheafification and universal properties belong to the ringed-site layer.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂))

/-- The `k`-th principal-parts module of `F` over `φ`, evaluated at `X`. -/
abbrev module (k : ℕ) (X : Cᵒᵖ) : ModuleCat (O₂.obj X) :=
  _root_.PrincipalParts.RingHom.module (φ.app X).hom (F.obj X) k

/-- The universal class of a section in the objectwise principal-parts module. -/
noncomputable abbrev universalClass (k : ℕ) (X : Cᵒᵖ) (m : F.obj X) :
    module φ F k X :=
  _root_.PrincipalParts.RingHom.universalClass (φ.app X).hom (F.obj X) k m

private theorem hom_ext_universalClass (k : ℕ) (X : Cᵒᵖ)
    {N : ModuleCat (O₂.obj X)} {f g : module φ F k X ⟶ N}
    (h : ∀ m : F.obj X,
      f.hom (universalClass φ F k X m) = g.hom (universalClass φ F k X m)) : f = g := by
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

/-- A restriction morphism of `F` induces the corresponding base-change morphism between its
sectionwise principal-parts modules. -/
noncomputable abbrev restrictionMap (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    module φ F k X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj (module φ F k Y) :=
  _root_.PrincipalParts.RingHom.BaseChange.map
    (φ.app X).hom (φ.app Y).hom (O₁.map f).hom (O₂.map f).hom
      (congrArg CommRingCat.Hom.hom (φ.naturality f)).symm k (F.map f)

/-- The restriction map on principal parts sends the universal class of a section to the
universal class of its restriction. -/
@[simp]
theorem restrictionMap_universalClass (k : ℕ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (m : F.obj X) :
    (restrictionMap φ F k f).hom (universalClass φ F k X m) =
      universalClass φ F k Y ((F.map f).hom m) := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  unfold restrictionMap _root_.PrincipalParts.RingHom.BaseChange.map
    _root_.PrincipalParts.BaseChange.moduleMap
  unfold _root_.PrincipalParts.BaseChange.Internal.mapFun _root_.PrincipalParts.BaseChange.map
  erw [_root_.PrincipalParts.representingEquiv_symm_apply_universalDifferential]
  rfl

/-- The restriction map on sectionwise principal parts preserves identity morphisms. -/
theorem restrictionMap_id (k : ℕ) (X : Cᵒᵖ) :
    restrictionMap φ F k (𝟙 X) =
      (ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app
          (module φ F k X) := by
  apply hom_ext_universalClass φ F k X
  intro m
  rw [restrictionMap_universalClass]
  change universalClass φ F k X ((F.map (𝟙 X)).hom m) = universalClass φ F k X m
  congr 1
  rw [F.map_id]
  rfl

/-- The restriction maps on sectionwise principal parts preserve composition. -/
theorem restrictionMap_comp (k : ℕ) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictionMap φ F k (f ≫ g) =
      restrictionMap φ F k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (restrictionMap φ F k g) ≫
        (ModuleCat.restrictScalarsComp' ((ringPresheaf O₂).map f).hom
          ((ringPresheaf O₂).map g).hom ((ringPresheaf O₂).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_comp f g))).inv.app
          (module φ F k Z) := by
  apply hom_ext_universalClass φ F k X
  intro m
  change (restrictionMap φ F k (f ≫ g)).hom (universalClass φ F k X m) =
    (restrictionMap φ F k g).hom
      ((restrictionMap φ F k f).hom (universalClass φ F k X m))
  rw [restrictionMap_universalClass, restrictionMap_universalClass,
    restrictionMap_universalClass]
  congr 1
  exact F.map_comp_apply f g m

/-- The presheaf of modules whose value at `X` is the explicit-ring-hom principal-parts module
`PrincipalParts.RingHom.module (φ.app X).hom (F.obj X) k`, with restriction maps induced by base
change. -/
@[stacks 09CL "presheaf principal parts"]
noncomputable abbrev presheaf (k : ℕ) : PresheafOfModules (ringPresheaf O₂) where
  obj X := module φ F k X
  map f := restrictionMap φ F k f
  map_id X := restrictionMap_id φ F k X
  map_comp f g := restrictionMap_comp φ F k f g

/-- The component of the universal differential from a module presheaf to its sectionwise
principal-parts presheaf. -/
noncomputable abbrev universalDifferentialApp (k : ℕ) (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      (PresheafOfModules.presheafStructureMap φ)).obj F).obj X ⟶
      ((PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap φ)).obj (presheaf φ F k)).obj X :=
  _root_.PrincipalParts.RingHom.universalDifferential
    (φ.app X).hom (F.obj X) k

/-- The objectwise universal differentials commute with restriction in the indexing
category. -/
theorem universalDifferentialApp_naturality (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap φ)).obj F).map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₁).map f).hom).map
          (universalDifferentialApp φ F k Y) =
      universalDifferentialApp φ F k X ≫
        ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap φ)).obj (presheaf φ F k)).map f := by
  ext m
  dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.restrictScalars.map_apply,
    universalDifferentialApp, _root_.PrincipalParts.RingHom.universalDifferential,
    ModuleCat.hom_ofHom]
  exact (restrictionMap_universalClass φ F k f m).symm

/-- The universal differential from a module presheaf to its sectionwise principal-parts
presheaf, linear after restriction to the source ring presheaf. -/
@[stacks 09CK "presheaf universal differential"]
noncomputable def universalDifferential (k : ℕ) :
    (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap φ)).obj F ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap φ)).obj (presheaf φ F k) where
  app X := universalDifferentialApp φ F k X
  naturality f := universalDifferentialApp_naturality φ F k f

/-- The universal presheaf differential has differential-operator order at most its
principal-parts order. -/
@[stacks 09CK "order bound for the presheaf universal differential"]
theorem universalDifferential_isOrderLE (k : ℕ) :
    PresheafOfModules.IsDifferentialOperatorOfOrder φ
      (universalDifferential φ F k) k := by
  intro X
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  change ModuleCat.IsDifferentialOperatorOfOrder (φ.app X).hom
    (_root_.PrincipalParts.RingHom.universalDifferential (φ.app X).hom (F.obj X) k) k
  unfold ModuleCat.IsDifferentialOperatorOfOrder _root_.PrincipalParts.RingHom.universalDifferential
  exact _root_.PrincipalParts.universalDifferential_isDifferentialOperatorOfOrder
    (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k

/-- Evaluating the universal presheaf differential at a site object gives the explicit
ring-hom universal differential. -/
@[simp]
theorem universalDifferential_app (k : ℕ) (X : Cᵒᵖ) :
    (universalDifferential φ F k).app X = universalDifferentialApp φ F k X := by
  rfl

section Functoriality

variable {G H : PresheafOfModules (ringPresheaf O₂)}

/-- The component on principal parts induced by a morphism of module presheaves. -/
noncomputable abbrev mapApp (k : ℕ) (α : F ⟶ G) (X : Cᵒᵖ) :
    module φ F k X ⟶ module φ G k X :=
  _root_.PrincipalParts.RingHom.map (φ.app X).hom k (α.app X)

/-- The component induced by a module-presheaf morphism preserves universal classes. -/
@[simp]
theorem mapApp_universalClass (k : ℕ) (α : F ⟶ G) (X : Cᵒᵖ) (m : F.obj X) :
    (mapApp φ F k α X).hom (universalClass φ F k X m) =
      universalClass φ G k X ((α.app X).hom m) := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  unfold mapApp _root_.PrincipalParts.RingHom.map
  rw [ModuleCat.hom_ofHom]
  unfold _root_.PrincipalParts.map
  erw [_root_.PrincipalParts.representingEquiv_symm_apply_universalDifferential]
  rfl

/-- The objectwise maps on principal parts are natural in the site object. -/
theorem mapApp_naturality (k : ℕ) (α : F ⟶ G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    restrictionMap φ F k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (mapApp φ F k α Y) =
      mapApp φ F k α X ≫ restrictionMap φ G k f := by
  apply hom_ext_universalClass φ F k X
  intro m
  change (mapApp φ F k α Y).hom
      ((restrictionMap φ F k f).hom (universalClass φ F k X m)) =
    (restrictionMap φ G k f).hom ((mapApp φ F k α X).hom (universalClass φ F k X m))
  rw [restrictionMap_universalClass, mapApp_universalClass, mapApp_universalClass,
    restrictionMap_universalClass]
  congr 1
  exact PresheafOfModules.naturality_apply α f m

/-- The morphism of principal-parts presheaves induced by a morphism of module presheaves. -/
noncomputable def map (k : ℕ) (α : F ⟶ G) : presheaf φ F k ⟶ presheaf φ G k where
  app X := mapApp φ F k α X
  naturality f := mapApp_naturality φ F k α f

/-- Principal-parts functoriality preserves identity morphisms of module presheaves. -/
@[simp]
theorem map_id (k : ℕ) : map φ F k (𝟙 F) = 𝟙 (presheaf φ F k) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply hom_ext_universalClass φ F k X
  intro m
  change (mapApp φ F k (𝟙 F) X).hom (universalClass φ F k X m) =
    universalClass φ F k X m
  rw [mapApp_universalClass]
  rfl

/-- Principal-parts functoriality preserves composition of module-presheaf morphisms. -/
@[simp]
theorem map_comp (k : ℕ) (α : F ⟶ G) (β : G ⟶ H) :
    map φ F k (α ≫ β) = map φ F k α ≫ map φ G k β := by
  apply PresheafOfModules.hom_ext
  intro X
  apply hom_ext_universalClass φ F k X
  intro m
  change (mapApp φ F k (α ≫ β) X).hom (universalClass φ F k X m) =
    (mapApp φ G k β X).hom ((mapApp φ F k α X).hom (universalClass φ F k X m))
  rw [mapApp_universalClass, mapApp_universalClass, mapApp_universalClass]
  rfl

/-- Principal parts of fixed order form an endofunctor on module presheaves. -/
noncomputable def functor (k : ℕ) :
    PresheafOfModules (ringPresheaf O₂) ⥤ PresheafOfModules (ringPresheaf O₂) where
  obj G := presheaf φ G k
  map α := map φ _ k α
  map_id G := map_id φ G k
  map_comp α β := map_comp φ _ k α β

end Functoriality

end PresheafOfModules.PrincipalParts
