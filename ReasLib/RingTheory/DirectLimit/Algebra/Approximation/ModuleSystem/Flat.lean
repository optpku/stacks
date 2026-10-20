/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Finiteness
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Pushout
public import ReasLib.Algebra.Module.Flat.Relative
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness in directed module systems

This leaf owns the source-faithful directed-system form of Lemma 10.168.1
(3).  The finite-presentation stage condition already entails finite
presentation of the limiting map and module by `ModuleSystem.Finiteness`, so
those source assumptions are not duplicated as public parameters here.
-/

@[expose] public section

universe u v x y

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Flatness of the limiting module is visible at one stage of a generic
directed module system with finitely presented stage maps and modules. -/
@[stacks 02JO "flatness at a directed module stage"]
theorem exists_flat_stage (A : ModuleSystem f M)
    (hfinitePresentation : A.hasFinitePresentation)
    (hflat : _root_.Module.FlatAlong f M) :
    ∃ i : A.index, _root_.Module.FlatAlong (A.map i) (A.moduleStage i) := sorry

/-- Flatness at one stage persists across a later module-system transition. -/
@[stacks 02JO "flatness at a directed module stage"]
theorem flat_later (A : ModuleSystem f M) {i j : A.index} (hij : i ≤ j)
    (hflat : _root_.Module.FlatAlong (A.map i) (A.moduleStage i)) :
    _root_.Module.FlatAlong (A.map j) (A.moduleStage j) := sorry

/-- Lemma 10.168.1 (3), tag `02JO`: in an arbitrary directed system of
finitely presented stage maps and modules with the stated base-change
isomorphisms, flatness is eventually visible at every stage. -/
@[stacks 02JO "eventual flatness in a directed module system"]
theorem eventually_flat (A : ModuleSystem f M)
    (hfinitePresentation : A.hasFinitePresentation)
    (hflat : _root_.Module.FlatAlong f M) :
    ∃ i₀ : A.index, ∀ j, i₀ ≤ j →
      _root_.Module.FlatAlong (A.map j) (A.moduleStage j) := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
