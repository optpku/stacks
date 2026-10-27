/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise sections and direct image on ringed sites

This leaf owns the underived section-ring map, restriction of scalars, and the natural
isomorphism identifying sections on a preimage object with sections after direct image.  Derived
comparison files build on this owner rather than recreating the underived map.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory Opposite

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The map on section rings induced by a morphism of ringed sites at `V`. -/
@[stacks 0D6H "section-ring map"]
abbrev sectionsRingMap.{u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    (f : X.Hom Y) (V : Y.carrier) :
    (Y.structureSheaf.obj.obj (op V) : Type w₁) →+*
      (X.structureSheaf.obj.obj (op (f.base.obj V)) : Type w₁) :=
  (f.structureSheafMap.1.app (op V)).hom

/-- Restriction of scalars along the section-ring map at `V`. -/
@[stacks 0D6H "section-ring restriction"]
abbrev sectionsRestriction.{z₁, u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    (f : X.Hom Y) (V : Y.carrier) :
    _root_.ModuleCat.{z₁} (X.structureSheaf.obj.obj (op (f.base.obj V))) ⥤
      _root_.ModuleCat.{z₁} (Y.structureSheaf.obj.obj (op V)) :=
  _root_.ModuleCat.restrictScalars.{z₁} (sectionsRingMap f V)

namespace ModuleSections

/-- The module-valued section functor at an object. -/
@[stacks 0D6H "sections at an object"]
abbrev objectFunctor (X : RingedSite.{uX, vX, w}) (V : X.carrier) :
    RingedSite.ModuleCat.{z} X ⥤
      _root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op V)) :=
  SheafOfModules.evaluation.{z} X.structureSheaf (op V)

/-- The identity on sections preserves addition between restricted and direct-image sections. -/
private theorem objectPushforwardNatApp_map_add (f : X.Hom Y) (V : Y.carrier)
    (F : RingedSite.ModuleCat.{z} X) :
    let M := (sectionsRestriction f V).obj ((objectFunctor.{z} X (f.base.obj V)).obj F)
    let N := (objectFunctor.{z} Y V).obj (f.modulePushforward.{z}.obj F)
    ∀ x y : M, ((x + y : M) : N) = (x : N) + (y : N) := fun _ _ => rfl

/-- The identity on sections respects the scalar action induced by the section-ring map. -/
private theorem objectPushforwardNatApp_map_smul (f : X.Hom Y) (V : Y.carrier)
    (F : RingedSite.ModuleCat.{z} X) :
    let M := (sectionsRestriction f V).obj ((objectFunctor.{z} X (f.base.obj V)).obj F)
    let N := (objectFunctor.{z} Y V).obj (f.modulePushforward.{z}.obj F)
    ∀ (r : Y.structureSheaf.obj.obj (op V)) (x : M),
      ((r • x : M) : N) = r • (x : N) := fun _ _ => rfl

/-- The objectwise component of direct-image naturality on module sections.  Its underlying map is
the identity on sections; only the scalar action changes. -/
@[stacks 0D6H "objectwise sections naturality"]
noncomputable def objectPushforwardNatApp (f : X.Hom Y) (V : Y.carrier)
    (F : RingedSite.ModuleCat.{z} X) :
    (sectionsRestriction f V).obj ((objectFunctor.{z} X (f.base.obj V)).obj F) ⟶
      (objectFunctor.{z} Y V).obj (f.modulePushforward.{z}.obj F) :=
  @ModuleCat.ofHom (Y.structureSheaf.obj.obj (op V)) _
    ((sectionsRestriction f V).obj
      ((objectFunctor.{z} X (f.base.obj V)).obj F) : Type _)
    ((objectFunctor.{z} Y V).obj (f.modulePushforward.{z}.obj F) : Type _)
    (ModuleCat.isAddCommGroup _)
    (ModuleCat.isModule _)
    (ModuleCat.isAddCommGroup _)
    (ModuleCat.isModule _)
    { toFun := fun x => x
      map_add' := objectPushforwardNatApp_map_add f V F
      map_smul' := objectPushforwardNatApp_map_smul f V F }

/-- The identity comparison of restricted and direct-image sections is natural in the module. -/
private theorem objectPushforwardNat_naturality (f : X.Hom Y) (V : Y.carrier)
    {F F' : RingedSite.ModuleCat.{z} X} (φ : F ⟶ F') :
    (objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V).map φ ≫
        objectPushforwardNatApp f V F' =
      objectPushforwardNatApp f V F ≫
        (f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V).map φ := by
  ext x
  rfl

/-- The underived natural transformation from restricted sections on a preimage object to
sections after direct image. -/
@[stacks 0D6H "objectwise sections naturality"]
noncomputable def objectPushforwardNat (f : X.Hom Y) (V : Y.carrier) :
    objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V ⟶
      f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V where
  app := objectPushforwardNatApp f V
  naturality _ _ φ := objectPushforwardNat_naturality f V φ

/-- The reverse objectwise comparison retains the section and restores its original scalar action. -/
noncomputable def objectPushforwardInvApp (f : X.Hom Y) (V : Y.carrier)
    (F : RingedSite.ModuleCat.{z} X) :
    (objectFunctor.{z} Y V).obj (f.modulePushforward.{z}.obj F) ⟶
      (sectionsRestriction f V).obj ((objectFunctor.{z} X (f.base.obj V)).obj F) :=
  @ModuleCat.ofHom (Y.structureSheaf.obj.obj (op V)) _
    ((objectFunctor.{z} Y V).obj (f.modulePushforward.{z}.obj F) : Type _)
    ((sectionsRestriction f V).obj
      ((objectFunctor.{z} X (f.base.obj V)).obj F) : Type _)
    (ModuleCat.isAddCommGroup _) (ModuleCat.isModule _)
    (ModuleCat.isAddCommGroup _) (ModuleCat.isModule _)
    { toFun := fun x => x
      map_add' := fun x y => (objectPushforwardNatApp_map_add f V F x y).symm
      map_smul' := fun r x => (objectPushforwardNatApp_map_smul f V F r x).symm }

/-- Sections after direct image map back to restricted sections on the preimage object. -/
noncomputable def objectPushforwardInv (f : X.Hom Y) (V : Y.carrier) :
    f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V ⟶
      objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V where
  app := objectPushforwardInvApp f V
  naturality F F' φ := by
    ext x
    rfl

/-- Objectwise sections commute with direct image after restriction of scalars. -/
@[stacks 0D6H "objectwise sections pushforward isomorphism"]
theorem objectPushforwardNat_isIso (f : X.Hom Y) (V : Y.carrier) :
    IsIso (objectPushforwardNat.{z} f V) := by
  refine ⟨⟨objectPushforwardInv f V, ?_, ?_⟩⟩
  · ext F x
    rfl
  · ext F x
    rfl

/-- The natural isomorphism between restricted sections on a preimage object and sections after
direct image. -/
@[stacks 0D6H "objectwise sections pushforward isomorphism"]
noncomputable def objectPushforwardIso (f : X.Hom Y) (V : Y.carrier) :
    objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V ≅
      f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V where
  hom := objectPushforwardNat f V
  inv := objectPushforwardInv f V
  hom_inv_id := by
    ext F x
    rfl
  inv_hom_id := by
    ext F x
    rfl

end ModuleSections

end RingedSite.Hom
