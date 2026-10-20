/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.RingTheory.Localization.Cardinality
public import ReasLib.Algebra.WLocalHull.WLocalization

/-!
# Cardinality of w-localization

Finite-stage algebras and the w-localization of a commutative ring have
cardinality bounded by any infinite cardinal bounding the original ring.
-/

@[expose] public section

universe u

open scoped Cardinal

namespace Algebra.WLocalHull

/-- Each finite-stage algebra `stage A E` has cardinality at most `κ` whenever
`κ` is infinite and `#A ≤ κ`. -/
theorem cardinalMk_stage_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (E : Finset A) : #(stage A E) ≤ κ :=
  sorry

/-- The w-localization `wLocalization A` has cardinality at most `κ` whenever
`κ` is infinite and `#A ≤ κ`. -/
theorem cardinalMk_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) : #(wLocalization A) ≤ κ :=
  sorry

/-- The cardinality of the w-localization is bounded by the maximum of the
countably infinite cardinal and the cardinality of the original ring. -/
theorem cardinalMk_le_max (A : Type u) [CommRing A] :
    #(wLocalization A) ≤ max ℵ₀ #A :=
  sorry

end Algebra.WLocalHull
