/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.AbsolutelyFlat
public import ReasLib.RingTheory.WeakDimension
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension-theoretic characterizations of absolutely flat rings

This file gathers the reusable characterizations of absolute flatness by weak dimension, reduced
Krull dimension zero, and fields at prime localizations.

@stack 092F
-/

@[expose] public section

open CategoryTheory

universe u

namespace IsAbsolutelyFlatRing

variable (R : Type u) [CommRing R]

/-- Absolute flatness is equivalent to weak dimension at most zero. -/
@[stacks 092F "weak dimension zero"]
theorem iff_hasWeakDimensionLE_zero :
    IsAbsolutelyFlatRing R ↔ HasWeakDimensionLE R 0 := sorry

/-- Absolute flatness is equivalent to being reduced of Krull dimension at most zero. -/
@[stacks 092F "reduced and zero-dimensional"]
theorem iff_isReduced_and_krullDimLE_zero :
    IsAbsolutelyFlatRing R ↔ IsReduced R ∧ Ring.KrullDimLE 0 R := sorry

/-- Absolute flatness is equivalent to all prime localizations being fields. -/
@[stacks 092F "local rings are fields"]
theorem iff_forall_isField_localizationAtPrime :
    IsAbsolutelyFlatRing R ↔
      ∀ p : PrimeSpectrum R, IsField (Localization.AtPrime p.asIdeal) := sorry

/-- An absolutely flat ring is reduced. -/
theorem isReduced [IsAbsolutelyFlatRing R] : IsReduced R := sorry

/-- An absolutely flat ring has Krull dimension at most zero. -/
theorem krullDimLE_zero [IsAbsolutelyFlatRing R] : Ring.KrullDimLE 0 R := sorry

/-- The four standard characterizations of an absolutely flat ring. -/
@[stacks 092F]
theorem tfae :
    List.TFAE
      [ HasWeakDimensionLE R 0,
        IsAbsolutelyFlatRing R,
        IsReduced R ∧ Ring.KrullDimLE 0 R,
        ∀ p : PrimeSpectrum R, IsField (Localization.AtPrime p.asIdeal) ] := sorry

end IsAbsolutelyFlatRing
