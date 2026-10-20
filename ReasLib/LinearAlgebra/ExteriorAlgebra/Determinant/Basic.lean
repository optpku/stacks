/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant submodules

@stack 0FJA

The determinant of a module is modeled as the submodule of its exterior algebra annihilated by
every degree-one generator.  The construction is meaningful for every module; finiteness,
projectivity, and rank belong only in later comparison theorems.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.Determinant

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Left multiplication by a degree-one generator of the exterior algebra. -/
@[stacks 0FJA "determinant action"]
def action (m : M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R m)

/-- The determinant submodule, consisting of elements annihilated by every degree-one
generator. -/
@[stacks 0FJA "determinant submodule"]
abbrev submodule : Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, (action R M m).ker

scoped[Module.Determinant] notation3:max "det[" R "](" M ")" =>
  _root_.Module.Determinant.submodule R M

open scoped Module.Determinant

/-- The canonical inclusion of the determinant submodule into the exterior algebra. -/
@[stacks 0FJA "determinant inclusion"]
abbrev ι : det[R](M) →ₗ[R] ExteriorAlgebra R M :=
  Submodule.subtype det[R](M)

variable {R M}

/-- Membership in the determinant is equivalent to annihilation by every degree-one
generator. -/
@[simp, stacks 0FJA "membership in the determinant submodule"]
theorem mem_iff (x : ExteriorAlgebra R M) :
    x ∈ det[R](M) ↔ ∀ m : M, ExteriorAlgebra.ι R m * x = 0 := sorry

/-- The determinant inclusion is annihilated by each degree-one action. -/
@[stacks 0FJA "determinant kernel equation"]
theorem ι_comp_action (m : M) :
    (action R M m).comp (ι R M) = 0 := sorry

/-- A linear map factors through the determinant exactly when every degree-one action
annihilates it. -/
@[stacks 0FJA "universal property of the determinant submodule"]
theorem range_le_iff {P : Type*} [AddCommGroup P] [Module R P]
    (f : P →ₗ[R] ExteriorAlgebra R M) :
    LinearMap.range f ≤ det[R](M) ↔
      ∀ m : M, (action R M m).comp f = 0 := sorry

/-- The canonical lift of a map whose range lies in the determinant submodule. -/
@[stacks 0FJA "lift to the determinant submodule"]
def lift {P : Type*} [AddCommGroup P] [Module R P]
    (f : P →ₗ[R] ExteriorAlgebra R M) (h : LinearMap.range f ≤ det[R](M)) :
    P →ₗ[R] det[R](M) :=
  f.codRestrict det[R](M) fun x => h (LinearMap.mem_range_self f x)

/-- The determinant lift recovers the original map after the canonical inclusion. -/
@[stacks 0FJA "determinant lift equation"]
theorem lift_ι {P : Type*} [AddCommGroup P] [Module R P]
    (f : P →ₗ[R] ExteriorAlgebra R M) (h : LinearMap.range f ≤ det[R](M)) :
    (ι R M).comp (lift f h) = f := sorry

/-- Maps into the determinant are determined by their composites with its inclusion. -/
@[ext, stacks 0FJA "determinant map extensionality"]
theorem hom_ext {P : Type*} [AddCommGroup P] [Module R P]
    {f g : P →ₗ[R] det[R](M)} (h : (ι R M).comp f = (ι R M).comp g) :
    f = g := sorry

end Module.Determinant

open scoped Module.Determinant
