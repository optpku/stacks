/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of rings for presheaves of modules

This file packages the same-base-category specialization of the general pullback/pushforward
adjunction for presheaves of modules.  The scalar morphism is exposed in the identity-base form
expected by the general API, while users of the fixed-base API see ordinary extension and
restriction of scalars.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace PresheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C]
variable {R R' : Cᵒᵖ ⥤ RingCat.{w}}

/-- A same-base morphism of ring presheaves in the identity-pushforward form used by the
general pullback API for presheaves of modules. -/
noncomputable abbrev homOverId (α : R ⟶ R') :
    R ⟶ (𝟭 C).op ⋙ R' :=
  α ≫ R'.leftUnitor.inv

/-- Pushforward along `homOverId α` is the ordinary restriction-of-scalars functor. -/
noncomputable def pushforwardIso (α : R ⟶ R') :
    PresheafOfModules.pushforward.{z} (homOverId α) ≅
      PresheafOfModules.restrictScalars.{z} α :=
  Iso.refl _

variable (α : R ⟶ R')
variable [(PresheafOfModules.pushforward.{z} (homOverId α)).IsRightAdjoint]

/-- Extension of scalars for presheaves of modules on a fixed base category. -/
noncomputable abbrev extension :
    PresheafOfModules.{z} R ⥤ PresheafOfModules.{z} R' :=
  PresheafOfModules.pullback.{z} (homOverId α)

/-- Extension of scalars for presheaves of modules is left adjoint to restriction of scalars. -/
@[stacks 03CU "adjunction"]
noncomputable def extensionRestrictionAdjunction :
    extension α ⊣ PresheafOfModules.restrictScalars.{z} α :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{z} (homOverId α)).ofNatIsoRight
    (pushforwardIso α)

/-- The canonical extension/restriction Hom equivalence for presheaves of modules. -/
noncomputable def extensionRestrictionHomEquiv
    (G : PresheafOfModules.{z} R) (F : PresheafOfModules.{z} R') :
    ((extension α).obj G ⟶ F) ≃
      (G ⟶ (PresheafOfModules.restrictScalars.{z} α).obj F) :=
  (extensionRestrictionAdjunction α).homEquiv G F

/-- Morphisms from `G` to the restriction of `F` correspond canonically to morphisms from the
extension of `G` to `F`. -/
@[stacks 03CU "Hom equivalence"]
noncomputable def restrictionExtensionHomEquiv
    (G : PresheafOfModules.{z} R) (F : PresheafOfModules.{z} R') :
    (G ⟶ (PresheafOfModules.restrictScalars.{z} α).obj F) ≃
      ((extension α).obj G ⟶ F) :=
  (extensionRestrictionHomEquiv α G F).symm

end PresheafOfModules.ChangeOfRings
