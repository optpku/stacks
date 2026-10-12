/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing directed module systems

This leaf owns pullback of a generic directed module system along an order
isomorphism.  The construction preserves the underlying ring approximation
and all module-system data without assuming finite-type or finite-module
conditions.  Base-change computations live in `ModuleSystem.Reindex.BaseChange`.
-/

@[expose] public section

universe u v x y z

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Reindex a directed module system along an order isomorphism. -/
@[stacks 00R1 "reindexed directed module system"]
noncomputable def reindex (A : ModuleSystem f M) {J : Type z}
    [Preorder J] (e : J ≃o A.index) : ModuleSystem f M where
  toHom := A.toHom.reindex e
  stageBaseChange_bijective := sorry
  moduleStage := fun j ↦ A.moduleStage (e j)
  moduleStage_addCommGroup := fun j ↦ A.moduleStage_addCommGroup (e j)
  moduleStage_module := fun j ↦ A.moduleStage_module (e j)
  moduleMap := fun {j k} h ↦ A.moduleMap (e.monotone h)
  moduleMap_id := fun j m ↦ A.moduleMap_id (e j) m
  moduleMap_comp := fun {j k l} hjk hkl m ↦
    A.moduleMap_comp (e.monotone hjk) (e.monotone hkl) m
  moduleToLimit := fun j ↦ A.moduleToLimit (e j)
  moduleToLimit_comp := fun {j k} h m ↦ A.moduleToLimit_comp (e.monotone h) m
  transitionBaseChange_spec := fun {j k} h ↦ sorry
  finalBaseChange_spec := fun _ ↦ sorry

/-- Reindexing pulls back the stage module family along the order isomorphism.
-/
@[simp, stacks 00R1 "reindexed directed module system"]
theorem reindex_moduleStage (A : ModuleSystem f M) {J : Type z} [Preorder J]
    (e : J ≃o A.index) (j : J) :
    (A.reindex e).moduleStage j = A.moduleStage (e j) := sorry

/-- A reindexed module transition is the original transition at the
corresponding comparable stages. -/
@[simp, stacks 00R1 "reindexed directed module system"]
theorem reindex_moduleMap (A : ModuleSystem f M) {J : Type z} [Preorder J]
    (e : J ≃o A.index) {j k : J} (h : j ≤ k) (m : A.moduleStage (e j)) :
    (A.reindex e).moduleMap h m = A.moduleMap (e.monotone h) m := sorry

/-- Reindexing preserves the maps from stage modules to the limiting module.
-/
@[simp, stacks 00R1 "reindexed directed module system"]
theorem reindex_moduleToLimit (A : ModuleSystem f M) {J : Type z} [Preorder J]
    (e : J ≃o A.index) (j : J) (m : A.moduleStage (e j)) :
    (A.reindex e).moduleToLimit j m = A.moduleToLimit (e j) m := sorry

/-- Forgetting module-system data commutes with reindexing. -/
@[simp, stacks 00R1 "reindexed directed module system"]
theorem reindex_toHom (A : ModuleSystem f M) {J : Type z} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).toHom = A.toHom.reindex e := sorry

/-- Finiteness of every stage module is preserved by reindexing. -/
@[stacks 02JO "reindexed finite directed module system"]
theorem reindex_hasFinite (A : ModuleSystem f M) (hA : A.hasFinite)
    {J : Type z} [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).hasFinite := sorry

/-- Stagewise finite presentation is preserved by reindexing a directed module
system along an order isomorphism. -/
@[stacks 02JO "reindexed finite-presentation directed module system"]
theorem reindex_hasFinitePresentation (A : ModuleSystem f M)
    (hA : A.hasFinitePresentation) {J : Type z} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).hasFinitePresentation := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
