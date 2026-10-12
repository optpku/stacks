/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

open CategoryTheory Opposite

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The map on section rings induced by a morphism of ringed sites at `V`. -/
@[stacks 0D6H "section-ring map"]
abbrev sectionsRingMap.{u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    (f : X.Hom Y) (V : Y) :
    (Y.structureSheaf.obj.obj (op V) : Type w₁) →+*
      (X.structureSheaf.obj.obj (op (f.base.obj V)) : Type w₁) :=
  (f.structureSheafMap.1.app (op V)).hom

/-- Restriction of scalars along the section-ring map at `V`. -/
@[stacks 0D6H "section-ring restriction"]
abbrev sectionsRestriction.{z₁, u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    (f : X.Hom Y) (V : Y) :
    _root_.ModuleCat.{z₁} (X.structureSheaf.obj.obj (op (f.base.obj V))) ⥤
      _root_.ModuleCat.{z₁} (Y.structureSheaf.obj.obj (op V)) :=
  _root_.ModuleCat.restrictScalars.{z₁} (sectionsRingMap f V)

namespace ModuleSections

/-- The module-valued section functor at an object. -/
@[stacks 0D6H "sections at an object"]
abbrev objectFunctor (X : RingedSite.{uX, vX, w}) (V : X) :
    RingedSite.ModuleCat.{z} X ⥤
      _root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op V)) :=
  SheafOfModules.evaluation.{z} X.structureSheaf (op V)

/-- The objectwise component of direct-image naturality on module sections.  Its underlying map is
the identity on sections; only the scalar action changes. -/
@[stacks 0D6H "objectwise sections naturality"]
noncomputable def objectPushforwardNatApp (f : X.Hom Y) (V : Y)
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
      map_add' := sorry
      map_smul' := sorry }

/-- The underived natural transformation from restricted sections on a preimage object to
sections after direct image. -/
@[stacks 0D6H "objectwise sections naturality"]
noncomputable def objectPushforwardNat (f : X.Hom Y) (V : Y) :
    objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V ⟶
      f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V where
  app := objectPushforwardNatApp f V
  naturality := sorry

/-- Objectwise sections commute with direct image after restriction of scalars. -/
@[stacks 0D6H "objectwise sections pushforward isomorphism"]
noncomputable instance objectPushforwardNat_isIso (f : X.Hom Y) (V : Y) :
    IsIso (objectPushforwardNat.{z} f V) := sorry

/-- The natural isomorphism between restricted sections on a preimage object and sections after
direct image. -/
@[stacks 0D6H "objectwise sections pushforward isomorphism"]
noncomputable def objectPushforwardIso (f : X.Hom Y) (V : Y) :
    objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V ≅
      f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V :=
  asIso (objectPushforwardNat f V)

end ModuleSections

end RingedSite.Hom
