/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Submodule
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential systems of ideal-power submodules

This leaf packages both the exact-exponent adic tower
`⋯ ⟶ I ^ 3 M ⟶ I ^ 2 M ⟶ I M ⟶ M` and its positive tail as sequential inverse
systems.  It is kept separate from the basic submodule API so consumers of a
single stage do not import inverse-system infrastructure.
@stack 0G3M
-/

@[expose] public section

open CategoryTheory
open Opposite

noncomputable section

universe u v

namespace Ideal.PowerSubmodule

variable {A : Type u} [CommRing A]

/-- The `n`th positive adic stage, namely `I ^ (n + 1) M`, as a bundled module. -/
@[stacks 0G3M "positive adic submodule stage"]
abbrev positiveStageObj
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) : ModuleCat.{v} A :=
  stageObj I M (n + 1)

/-- The successor transition `I ^ (n + 2) M ⟶ I ^ (n + 1) M`. -/
@[stacks 0G3M "positive adic submodule transition"]
abbrev positiveStep
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    positiveStageObj I M (n + 1) ⟶ positiveStageObj I M n :=
  inclusion I M (Nat.le_succ (n + 1))

/-- The positive sequential inverse system `(I ^ (n + 1) M)ₙ`. -/
@[stacks 0G3M "positive adic submodule inverse system"]
abbrev positiveSystem
    (I : Ideal A) (M : ModuleCat.{v} A) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  Functor.ofOpSequence (positiveStep I M)

/-- The exact-exponent adic inverse system `(I ^ n M)ₙ`. -/
abbrev system
    (I : Ideal A) (M : ModuleCat.{v} A) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  Functor.ofOpSequence (X := fun n ↦ stageObj I M n)
    (fun n ↦ inclusion I M (Nat.le_succ n))

/-- The object formula for the positive adic submodule system. -/
@[simp, stacks 0G3M "positive adic submodule system object"]
theorem positiveSystem_obj
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    (positiveSystem I M).obj (op n) = positiveStageObj I M n := sorry

/-- The successor-map formula for the positive adic submodule system. -/
@[simp, stacks 0G3M "positive adic submodule system transition"]
theorem positiveSystem_stepMap
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    (positiveSystem I M).stepMap n = positiveStep I M n := sorry

/-- The object formula for the exact-exponent adic submodule system. -/
@[simp]
theorem system_obj
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    (system I M).obj (op n) = stageObj I M n := sorry

/-- Every exact-exponent adic transition is the canonical deeper-to-shallower inclusion. -/
@[simp]
theorem system_transitionMap
    (I : Ideal A) (M : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    (system I M).transitionMap h = inclusion I M h := sorry

end Ideal.PowerSubmodule
