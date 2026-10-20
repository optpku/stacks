/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally surjective coefficient maps and module pushforward

A locally surjective morphism of ring sheaves makes the canonical structure-module map onto
the pushed-forward unit module an epimorphism. This is the module-level quotient bridge used by
closed immersions and change-of-rings arguments.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' v' w

namespace SheafOfModules.PushforwardContinuous

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [F.IsContinuous J K]
variable {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}

/-- A locally surjective coefficient map induces an epimorphism from the unit module to the
pushed-forward unit module. -/
@[stacks 01C2 "structure module quotient"]
instance unitMap_epi
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    [Sheaf.IsLocallySurjective φ] :
    Epi (SheafOfModules.unitToPushforwardObjUnit φ) := sorry

end SheafOfModules.PushforwardContinuous
