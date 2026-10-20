/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DifferentialOperator
public import ReasLib.RingTheory.Kaehler.DeRham.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential-operator order of algebraic de Rham differentials

The algebraic de Rham differential is first order relative to the target-ring
action.  This leaf records the fact directly for the bundled source-restricted
modules and for morphisms in `CommRingCat`.
-/

@[expose] public section

universe u

namespace KaehlerDifferential.DeRham

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The algebraic de Rham differential on presented Kähler forms is a
differential operator of order at most one. -/
@[stacks 0G34 "order of the algebraic de Rham differential"]
theorem d_isOrderOne (p : ℕ) :
    ModuleCat.IsDifferentialOperatorOfOrder (algebraMap A B) (d A B p) 1 := sorry

end KaehlerDifferential.DeRham

namespace CommRingCat.DeRham

variable {A B : CommRingCat.{u}}

/-- The categorical algebraic de Rham differential is a differential operator
of order at most one along its ring morphism. -/
@[stacks 0G34 "order of the categorical de Rham differential"]
theorem d_isOrderOne (f : A ⟶ B) (p : ℕ) :
    ModuleCat.IsDifferentialOperatorOfOrder f.hom (d f p) 1 := sorry

end CommRingCat.DeRham
