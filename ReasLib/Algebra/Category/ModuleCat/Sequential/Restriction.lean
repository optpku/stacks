/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sequential
public import ReasLib.CategoryTheory.InverseSystem.Cone
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting a varying-ring module system to a cone vertex

A cone over a sequential system of commutative rings is precisely a compatible family of maps
from one fixed ring to every stage.  Restriction of scalars along its legs turns a varying-ring
module object into an ordinary sequential inverse system over the cone vertex.
@stack 091D
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

/-! ### Fixed-vertex restriction -/

/-- The stage-`n` evaluation of a varying-ring module system, restricted to a cone vertex. -/
@[stacks 091D "cone-vertex restriction of a varying-ring evaluation"]
abbrev restrictEvaluation
    (F : SequentialInverseSystem CommRingCat.{u}) (s : Cone F) (n : ℕ) :
    ModuleSystem.{u, v} F ⥤ ModuleCat.{v} (s.pt : Type u) :=
  evaluation F n ⋙ ModuleCat.restrictScalars (s.stageMap n).hom

/-- The successor map between evaluations restricted to a cone vertex. -/
@[stacks 091D "successor map of a cone-vertex restricted evaluation"]
noncomputable def restrictEvaluationStep
    (F : SequentialInverseSystem CommRingCat.{u}) (s : Cone F) (n : ℕ) :
    restrictEvaluation F s (n + 1) ⟶ restrictEvaluation F s n :=
  Functor.whiskerRight (evaluationStep F n)
      (ModuleCat.restrictScalars (s.stageMap (n + 1)).hom) ≫
    Functor.whiskerLeft (evaluation F n)
      ((ModuleCat.restrictScalarsComp'
        (s.stageMap (n + 1)).hom (F.stepMap n).hom (s.stageMap n).hom
        (congrArg CommRingCat.Hom.hom (s.stageMap_step n)).symm).inv)

/-- The fixed-ring inverse system obtained by restricting a varying-ring module object to a
cone vertex. -/
@[stacks 091D "cone-vertex restriction tower of a varying-ring module"]
noncomputable def restrictTower
    (F : SequentialInverseSystem CommRingCat.{u}) (s : Cone F)
    (T : ModuleSystem.{u, v} F) :
    SequentialInverseSystem (ModuleCat.{v} (s.pt : Type u)) :=
  @Functor.ofOpSequence (ModuleCat.{v} (s.pt : Type u)) _
    (fun n ↦ (restrictEvaluation F s n).obj T)
    (fun n ↦ (restrictEvaluationStep F s n).app T)

/-- The object formula for a cone-vertex restriction tower. -/
@[simp, stacks 091D "object formula for a cone-vertex restriction tower"]
theorem restrictTower_obj
    (F : SequentialInverseSystem CommRingCat.{u}) (s : Cone F)
    (T : ModuleSystem.{u, v} F) (n : ℕ) :
    (restrictTower F s T).obj (op n) = (restrictEvaluation F s n).obj T := sorry

/-- The successor-map formula for a cone-vertex restriction tower. -/
@[stacks 091D "transition formula for a cone-vertex restriction tower"]
theorem restrictTower_stepMap
    (F : SequentialInverseSystem CommRingCat.{u}) (s : Cone F)
    (T : ModuleSystem.{u, v} F) (n : ℕ) :
    (restrictTower F s T).stepMap n = (restrictEvaluationStep F s n).app T := sorry

end CategoryTheory.SequentialInverseSystem

end
