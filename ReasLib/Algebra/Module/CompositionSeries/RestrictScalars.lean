/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.CompositionSeries.Factor

/-!
# Composition series under restriction of scalars

This file owns the additive length API obtained by viewing a composition
series over an algebra as a filtration over its base ring.

@stack 02M0
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace Module.CompositionSeries

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [Ring B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- One step of a composition series adds the base-ring length of its factor. -/
@[stacks 02M0 "one composition-series step under restriction of scalars"]
theorem stepLength_eq_add_factorLength
    (s : CompositionSeries (Submodule B M)) (i : Fin s.length) :
    Module.length A ((s i.succ).restrictScalars A) =
      Module.length A ((s i.castSucc).restrictScalars A) +
        Module.length A (factor s i) := sorry

/-- The base-ring length of a module is the sum of the base-ring lengths of the factors in any
composition series from `⊥` to `⊤`. -/
@[stacks 02M0 "composition-series length under restriction of scalars"]
theorem length_eq_sum_factorLength
    (s : CompositionSeries (Submodule B M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) :
    Module.length A M = ∑ i : Fin s.length, Module.length A (factor s i) := sorry

end Module.CompositionSeries
