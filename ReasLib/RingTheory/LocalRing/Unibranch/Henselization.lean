/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Ideal.MinimalPrime.Flat
public import ReasLib.RingTheory.LocalRing.Unibranch.MinimalPrime
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unibranchness and Henselizations

This file characterizes a unibranch local ring by the generic points of any Henselization. The
equivalence is the canonical API; the two directions are also named for downstream use.
@stack 0BQ0
-/

@[expose] public section

open Ideal

universe u v

namespace IsUnibranch.Henselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- A local ring is unibranch exactly when any Henselization has a unique minimal prime. -/
@[stacks 0BQ0 "unibranch Henselization criterion"]
theorem iff_uniqueMinimalPrime :
    IsUnibranch A ↔ ∃! p : Ideal Ah, p ∈ minimalPrimes Ah := sorry

/-- A Henselization of a unibranch local ring has a unique minimal prime. -/
@[stacks 0BQ0 "unique minimal prime of a Henselization"]
theorem uniqueMinimalPrime [IsUnibranch A] :
    ∃! p : Ideal Ah, p ∈ minimalPrimes Ah := sorry

/-- A local ring is unibranch if one of its Henselizations has a unique minimal prime. -/
@[stacks 0BQ0 "unibranchness from a Henselization"]
theorem of_uniqueMinimalPrime
    (h : ∃! p : Ideal Ah, p ∈ minimalPrimes Ah) :
    IsUnibranch A := sorry

end IsUnibranch.Henselization
