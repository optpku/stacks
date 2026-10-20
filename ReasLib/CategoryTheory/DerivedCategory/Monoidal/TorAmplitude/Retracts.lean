/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.ObjectProperty.Retract.Lattice

/-!
# Retracts of objects with bounded Tor-amplitude

@stack 08G3
@stack 066G

Tor-amplitude bounds are detected after applying functors and taking homology, so they descend
to retracts.  This leaf exposes that fact at the `ObjectProperty` level and derives the common
direct-summand interface.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.DerivedTensor

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [Right.Has (C := C)]

/-- Lower Tor-amplitude descends to retracts. -/
@[stacks 08G3 "lower-bound retract stability, abstract monoidal form"]
instance torAmplitudeGE_isStableUnderRetracts (a : ℤ) :
    (torAmplitudeGE (C := C) a).IsStableUnderRetracts := sorry
/- Proof strategy: fixed-right derived tensor preserves retract diagrams, and `IsGE` is stable
under retracts. -/

/-- Upper Tor-amplitude descends to retracts. -/
@[stacks 08G3 "upper-bound retract stability, abstract monoidal form"]
instance torAmplitudeLE_isStableUnderRetracts (b : ℤ) :
    (torAmplitudeLE (C := C) b).IsStableUnderRetracts := sorry
/- Proof strategy: fixed-right derived tensor preserves retract diagrams, and `IsLE` is stable
under retracts. -/

/-- A retract of an object with lower Tor-amplitude at least `a` has the same lower bound. -/
@[stacks 08G3 "lower Tor-amplitude under retract"]
theorem HasTorAmplitudeGE.ofRetract
    {K L : DerivedCategory C} {a : ℤ} (r : Retract K L) (hL : HasTorAmplitudeGE L a) :
    HasTorAmplitudeGE K a := sorry
/- Proof strategy: apply `torAmplitudeGE_isStableUnderRetracts` to `r` and `hL`. -/

/-- A retract of an object with upper Tor-amplitude at most `b` has the same upper bound. -/
@[stacks 08G3 "upper Tor-amplitude under retract"]
theorem HasTorAmplitudeLE.ofRetract
    {K L : DerivedCategory C} {b : ℤ} (r : Retract K L) (hL : HasTorAmplitudeLE L b) :
    HasTorAmplitudeLE K b := sorry
/- Proof strategy: apply `torAmplitudeLE_isStableUnderRetracts` to `r` and `hL`. -/

/-- A retract of an object with Tor-amplitude in `[a, b]` has the same bound. -/
@[stacks 08G3 "Tor-amplitude interval under retract"]
theorem HasTorAmplitudeIn.ofRetract
    {K L : DerivedCategory C} {a b : ℤ} (r : Retract K L)
    (hL : HasTorAmplitudeIn L a b) :
    HasTorAmplitudeIn K a b := sorry
/- Proof strategy: project the interval into lower and upper bounds, transport each across the
retract, and recombine them. -/

/-- A retract of an object of finite Tor dimension again has finite Tor dimension. -/
@[stacks 08G3 "finite Tor dimension under retract"]
theorem HasFiniteTorDimension.ofRetract
    {K L : DerivedCategory C} (r : Retract K L) (hL : HasFiniteTorDimension L) :
    HasFiniteTorDimension K := sorry
/- Proof strategy: choose an interval witnessing `hL` and transport that interval across the
retract with `HasTorAmplitudeIn.ofRetract`. -/

namespace TorAmplitude

/-- Lemma 15.67.7 (Stacks `066G`), equivalently Lemma 21.46.8: if a biproduct has
Tor-amplitude in `[a, b]`, then both summands have Tor-amplitude in `[a, b]`. -/
@[stacks 08G3 "abstract monoidal form", stacks 066G]
theorem summands_of_biprod
    (K L : DerivedCategory C) [HasBinaryBiproduct K L] {a b : ℤ}
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b ∧ HasTorAmplitudeIn L a b := sorry
/- Proof strategy: apply `HasTorAmplitudeIn.ofRetract` to the canonical left and right biproduct
retracts. -/

/-- The left summand of a biproduct inherits its Tor-amplitude interval. -/
@[stacks 066G "left biproduct summand"]
theorem left_of_biprod
    (K L : DerivedCategory C) [HasBinaryBiproduct K L] {a b : ℤ}
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b := sorry
/- Proof strategy: project the left component of `summands_of_biprod`. -/

/-- The right summand of a biproduct inherits its Tor-amplitude interval. -/
@[stacks 066G "right biproduct summand"]
theorem right_of_biprod
    (K L : DerivedCategory C) [HasBinaryBiproduct K L] {a b : ℤ}
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b := sorry
/- Proof strategy: project the right component of `summands_of_biprod`. -/

end TorAmplitude

end

end CategoryTheory.DerivedCategory.DerivedTensor
