/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Finite products and the zero object in `FGModuleCat`

Finitely generated modules are closed under finite products over an arbitrary
ring, so `FGModuleCat` has finite products and a zero object without a
Noetherian hypothesis.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace FGModuleCat

variable (R : Type u) [Ring R]

/-- Finite products exist in `FGModuleCat R` for an arbitrary ring `R`. -/
instance instHasFiniteProducts : HasFiniteProducts (FGModuleCat.{v} R) := sorry

/-- The finitely generated zero module is a zero object of `FGModuleCat R`. -/
theorem isZero_ofPUnit : IsZero (of R (PUnit : Type v)) := sorry

/-- The zero object of `FGModuleCat R` is the zero module. -/
instance instHasZeroObject : HasZeroObject (FGModuleCat.{v} R) where
  zero := ⟨of R PUnit, isZero_ofPUnit R⟩

end FGModuleCat
