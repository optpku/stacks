/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Specialization
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Reindex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing finite-module approximations

This compatibility leaf retains the finite-type and finite-module data that a
generic `ModuleSystem.reindex` does not carry.  All directed module-system
data are owned by `ModuleSystem.reindex`.
-/

@[expose] public section

universe u v w x y z

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Module

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Reindex a finite-module approximation along an order isomorphism, retaining
the extra finite-type and finite-stage-module fields.  The directed
module-system data are supplied by `ModuleSystem.reindex`. -/
@[stacks 00R1 "reindexed finite module approximation"]
noncomputable def reindex (A : Module f M) {J : Type z}
    [Preorder J] (e : J ≃o A.index) : Module f M :=
  let B : ModuleSystem f M := A.toSystem.reindex e
  { toFiniteType := A.toFiniteType.reindex e
    stageBaseChange_bijective := B.stageBaseChange_bijective
    moduleStage := B.moduleStage
    moduleStage_addCommGroup := B.moduleStage_addCommGroup
    moduleStage_module := B.moduleStage_module
    moduleStage_finite := fun j ↦ A.moduleStage_finite (e j)
    moduleMap := B.moduleMap
    moduleMap_id := B.moduleMap_id
    moduleMap_comp := B.moduleMap_comp
    moduleToLimit := B.moduleToLimit
    moduleToLimit_comp := B.moduleToLimit_comp
    transitionBaseChange_bijective := sorry
    finalBaseChange_bijective := sorry }

/-- Forgetting the finite-type fields after reindexing recovers the generic
module-system reindexing. -/
@[stacks 00R1 "reindexed finite module approximation compatibility"]
theorem reindex_toSystem (A : Module f M) {J : Type z} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).toSystem = A.toSystem.reindex e := sorry

/-- Forgetting module data commutes with reindexing. -/
@[simp, stacks 00R1 "reindexed finite module approximation"]
theorem reindex_toFiniteType (A : Module f M) {J : Type z} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).toFiniteType = A.toFiniteType.reindex e := sorry

end Module

end Ring.DirectLimit.Algebra.Approximation
