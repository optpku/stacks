/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal tails of directed module systems

This leaf owns restriction of a generic directed module system to a cofinal
tail.  It does not require finite-type or finite-module data; the latter are
preserved by the compatibility constructor in `Approximation.Module.Tail`.
Base-change map computations live in `ModuleSystem.Tail.BaseChange`.
-/

@[expose] public section

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Restrict a directed module system to the cofinal tail above `i₀`.  The
underlying directed ring approximation and all module transition data are
pulled back along the subtype inclusion. -/
@[stacks 00R1 "directed module-system tail"]
noncomputable def tail (A : ModuleSystem f M) (i₀ : A.index) : ModuleSystem f M where
  toHom := A.toHom.tail i₀
  stageBaseChange_bijective := sorry
  moduleStage := fun j ↦ A.moduleStage j.1
  moduleStage_addCommGroup := fun j ↦ A.moduleStage_addCommGroup j.1
  moduleStage_module := fun j ↦ A.moduleStage_module j.1
  moduleMap := fun {j k} h ↦ A.moduleMap h
  moduleMap_id := fun j m ↦ A.moduleMap_id j.1 m
  moduleMap_comp := fun {j k l} hjk hkl m ↦ A.moduleMap_comp hjk hkl m
  moduleToLimit := fun j ↦ A.moduleToLimit j.1
  moduleToLimit_comp := fun {j k} h m ↦ A.moduleToLimit_comp h m
  transitionBaseChange_spec := fun {j k} h ↦ sorry
  finalBaseChange_spec := fun _ ↦ sorry

/-- The stage module of a tail system is the original stage module at the
underlying index. -/
@[simp, stacks 00R1 "directed module-system tail"]
theorem tail_moduleStage (A : ModuleSystem f M) (i₀ : A.index) (j : Set.Ici i₀) :
    (A.tail i₀).moduleStage j = A.moduleStage j.1 := sorry

/-- A module transition in a tail system is the original transition at the
underlying comparable stages. -/
@[simp, stacks 00R1 "directed module-system tail"]
theorem tail_moduleMap (A : ModuleSystem f M) (i₀ : A.index)
    {j k : Set.Ici i₀} (h : j ≤ k) (m : A.moduleStage j.1) :
    (A.tail i₀).moduleMap h m = A.moduleMap h m := sorry

/-- The map from a tail stage module to the limiting module is the original
stage-to-limit map. -/
@[simp, stacks 00R1 "directed module-system tail"]
theorem tail_moduleToLimit (A : ModuleSystem f M) (i₀ : A.index)
    (j : Set.Ici i₀) (m : A.moduleStage j.1) :
    (A.tail i₀).moduleToLimit j m = A.moduleToLimit j.1 m := sorry

/-- Forgetting module-system data commutes with restricting to a cofinal tail.
-/
@[simp, stacks 00R1 "directed module-system tail"]
theorem tail_toHom (A : ModuleSystem f M) (i₀ : A.index) :
    (A.tail i₀).toHom = A.toHom.tail i₀ := sorry

/-- Finiteness of every stage module is preserved by restricting to a cofinal
tail. -/
@[stacks 02JO "finite directed module-system tail"]
theorem tail_hasFinite (A : ModuleSystem f M) (hA : A.hasFinite) (i₀ : A.index) :
    (A.tail i₀).hasFinite := sorry

/-- Stagewise finite presentation is preserved by restricting a directed
module system to a cofinal tail. -/
@[stacks 02JO "finite-presentation directed module-system tail"]
theorem tail_hasFinitePresentation (A : ModuleSystem f M)
    (hA : A.hasFinitePresentation) (i₀ : A.index) :
    (A.tail i₀).hasFinitePresentation := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
