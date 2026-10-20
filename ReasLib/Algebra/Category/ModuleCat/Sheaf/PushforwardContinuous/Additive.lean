/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Additivity of pushforward for sheaves of modules

Pushforward along a continuous functor and a compatible map of ring sheaves is
additive.  Registering this at the generic module-sheaf layer lets composite
section functors obtain additivity from typeclass search, without rebuilding an
objectwise proof at each ringed-site application.
-/

@[expose] public section

open CategoryTheory

universe u v uC vC uD vD

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable [F.IsContinuous J K]

/-- Pushforward of sheaves of modules along a continuous morphism of ring
sheaves is additive. -/
instance pushforward_additive
    (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (pushforward.{v} phi).Additive := sorry

end SheafOfModules
