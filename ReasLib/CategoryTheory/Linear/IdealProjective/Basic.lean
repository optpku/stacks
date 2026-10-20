/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.CategoryTheory.ObjectProperty.FactorThrough

@[expose] public section

/-!
# Ideal-projective objects in a linear category

@stack 0G93

An object is `I`-projective when each scalar endomorphism indexed by `I` factors through a
projective object.  This is the category-level owner; module-specific formulations are
specializations which additionally package the set of good scalars as an ideal.
-/

universe w v u

namespace CategoryTheory

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The objects whose scalar endomorphisms from `I` factor through projective objects. -/
@[stacks 0G93 "ideal-projectivity in a linear category"]
def idealProjective (I : Ideal R) : ObjectProperty C :=
  fun X ↦ ∀ a : I, (isProjective C).factorThru ((a : R) • 𝟙 X)

/-- Pointwise characterization of `idealProjective`. -/
theorem idealProjective_iff (I : Ideal R) (X : C) :
    idealProjective (C := C) I X ↔
      ∀ a : I, (isProjective C).factorThru ((a : R) • 𝟙 X) := sorry

/-- Ideal-projectivity is contravariantly monotone in the ideal. -/
theorem idealProjective_mono {I J : Ideal R} (hJI : J ≤ I) :
    idealProjective (C := C) I ≤ idealProjective (C := C) J := sorry

/-- A projective object is ideal-projective for every ideal. -/
theorem idealProjective_of_projective (I : Ideal R) (X : C) [Projective X] :
    idealProjective (C := C) I X := sorry

end CategoryTheory
