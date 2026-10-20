/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves annihilated by the kernel of a structure map

For a structure map `φ : S ⟶ F_* R`, the kernel acts on an `S`-module sheaf sectionwise.
The predicate in this file is independent of any closed-immersion hypothesis and works for an
arbitrary continuous map of sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v v₁ v₂ u₁ u₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable [F.IsContinuous J K]

/-- An `S`-module sheaf is annihilated by the kernel of `φ : S ⟶ F_* R` when every local
scalar mapped to zero acts by zero. -/
@[stacks 08M3 "kernel-annihilation predicate"]
def IsAnnihilatedByKernel
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (M : SheafOfModules.{v} S) : Prop :=
  ∀ U : Cᵒᵖ, ∀ r : S.obj.obj U, ∀ m : M.val.obj U,
    φ.hom.app U r = 0 → r • m = 0

namespace IsAnnihilatedByKernel

/-- Kernel annihilation can equivalently be tested on the sections of the kernel submodule of
the source structure sheaf. -/
theorem iff_kernel_smul_eq_zero
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (M : SheafOfModules.{v} S) :
    IsAnnihilatedByKernel φ M ↔
      ∀ U : Cᵒᵖ,
        ∀ r : (kernel (unitToPushforwardObjUnit φ)).val.obj U,
          ∀ m : M.val.obj U,
            ((kernel.ι (unitToPushforwardObjUnit φ)).val.app U r) • m = 0 := sorry

/-- Kernel annihilation is invariant under isomorphism of module sheaves. -/
theorem iff_of_iso
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {M N : SheafOfModules.{v} S} (e : M ≅ N) :
    IsAnnihilatedByKernel φ M ↔ IsAnnihilatedByKernel φ N := sorry

/-- The kernel-annihilation object property is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsAnnihilatedByKernel φ : ObjectProperty (SheafOfModules.{v} S)) := sorry

/-- Every pushed-forward module sheaf is annihilated by the kernel of the structure map. -/
theorem of_pushforward
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (N : SheafOfModules.{v} R) :
    IsAnnihilatedByKernel φ ((pushforward φ).obj N) := sorry

/-- Every object in the essential image of module pushforward is annihilated by the kernel of
the structure map. -/
theorem of_mem_essImage
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {M : SheafOfModules.{v} S} (hM : (pushforward φ).essImage M) :
    IsAnnihilatedByKernel φ M := sorry

end IsAnnihilatedByKernel

end SheafOfModules
