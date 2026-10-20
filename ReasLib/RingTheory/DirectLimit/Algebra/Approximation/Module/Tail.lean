/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Specialization
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Tail
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal tails of finite-module approximations

This compatibility leaf retains the finite-type and finite-module data that a
generic `ModuleSystem.tail` does not carry.  All directed module-system data
are owned by `ModuleSystem.tail`.
-/

@[expose] public section

universe u v w x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Module

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Restrict a finite-module approximation to a cofinal tail, retaining the
extra finite-type and finite-stage-module fields.  The directed module-system
data are supplied by the generic `ModuleSystem.tail` owner. -/
@[stacks 00R1 "finite module approximation tail"]
noncomputable def tail (A : Module f M) (i₀ : A.index) : Module f M :=
  let B : ModuleSystem f M := A.toSystem.tail i₀
  { toFiniteType := A.toFiniteType.tail i₀
    stageBaseChange_bijective := B.stageBaseChange_bijective
    moduleStage := B.moduleStage
    moduleStage_addCommGroup := B.moduleStage_addCommGroup
    moduleStage_module := B.moduleStage_module
    moduleStage_finite := fun j ↦ A.moduleStage_finite j.1
    moduleMap := B.moduleMap
    moduleMap_id := B.moduleMap_id
    moduleMap_comp := B.moduleMap_comp
    moduleToLimit := B.moduleToLimit
    moduleToLimit_comp := B.moduleToLimit_comp
    transitionBaseChange_bijective := sorry
    finalBaseChange_bijective := sorry }

/-- Forgetting the finite-type fields after taking a tail recovers the generic
module-system tail. -/
@[stacks 00R1 "finite module approximation tail compatibility"]
theorem tail_toSystem (A : Module f M) (i₀ : A.index) :
    (A.tail i₀).toSystem = A.toSystem.tail i₀ := sorry

/-- Forgetting module data commutes with restricting to a tail. -/
@[simp, stacks 00R1 "finite module approximation tail"]
theorem tail_toFiniteType (A : Module f M) (i₀ : A.index) :
    (A.tail i₀).toFiniteType = A.toFiniteType.tail i₀ := sorry

end Module

end Ring.DirectLimit.Algebra.Approximation
