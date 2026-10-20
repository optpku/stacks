/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Algebraic closures of finite fields
-/

@[expose] public section

noncomputable section

universe u

/-- A field is an algebraic closure of a finite field. -/
def IsAlgebraicClosureOfFiniteField (k : Type u) [Field k] : Prop :=
  ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra F k), IsAlgClosure F k

/-- A field is an algebraic closure of a finite field exactly when some finite field
admits an algebra structure over which it is an algebraic closure. -/
theorem IsAlgebraicClosureOfFiniteField_iff (k : Type u) [Field k] :
    IsAlgebraicClosureOfFiniteField k ↔
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra F k), IsAlgClosure F k :=
  Iff.rfl
