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
# Geometric unibranchness and strict Henselizations

This file characterizes a geometrically unibranch local ring by the generic points of any strict
Henselization. The equivalence is the canonical API; the two directions are also named so callers
with either a typeclass hypothesis or an explicit uniqueness witness need no local repackaging.
@stack 06DM
-/

@[expose] public section

open Ideal

universe u v

namespace IsGeometricallyUnibranch.StrictHenselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ash : Type v} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- A local ring is geometrically unibranch exactly when any strict Henselization has a unique
minimal prime. -/
@[stacks 06DM "geometrically unibranch strict Henselization criterion"]
theorem iff_uniqueMinimalPrime :
    IsGeometricallyUnibranch A ↔ ∃! p : Ideal Ash, p ∈ minimalPrimes Ash := sorry

/-- A strict Henselization of a geometrically unibranch local ring has a unique minimal prime. -/
@[stacks 06DM "unique minimal prime of a strict Henselization"]
theorem uniqueMinimalPrime [IsGeometricallyUnibranch A] :
    ∃! p : Ideal Ash, p ∈ minimalPrimes Ash := sorry

/-- A local ring is geometrically unibranch if one of its strict Henselizations has a unique
minimal prime. -/
@[stacks 06DM "geometric unibranchness from a strict Henselization"]
theorem of_uniqueMinimalPrime
    (h : ∃! p : Ideal Ash, p ∈ minimalPrimes Ash) :
    IsGeometricallyUnibranch A := sorry

end IsGeometricallyUnibranch.StrictHenselization
