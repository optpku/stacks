/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude
public import ReasLib.CategoryTheory.ObjectProperty.Retract.Lattice

/-!
# Retracts of objects with bounded injective amplitude

Bounded complexes of injectives are K-injective, and the bounded homotopy category of injectives
is idempotent complete.  Thus injective amplitude descends to retracts without an ambient
enough-injectives assumption.  This leaf exposes both fixed-interval and finite-dimension forms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Fixed injective amplitude descends to retracts. -/
instance injectiveAmplitudeIn_isStableUnderRetracts (a b : ℤ) :
    (injectiveAmplitudeIn (C := C) a b).IsStableUnderRetracts := sorry

/-- A retract of an object with injective amplitude in `[a, b]` has the same bound. -/
theorem HasInjectiveAmplitudeIn.ofRetract
    {K L : DerivedCategory C} {a b : ℤ} (r : Retract K L)
    (hL : HasInjectiveAmplitudeIn L a b) :
    HasInjectiveAmplitudeIn K a b := sorry

/-- Finite injective dimension descends to retracts. -/
instance finiteInjectiveDimension_isStableUnderRetracts :
    (finiteInjectiveDimension (C := C)).IsStableUnderRetracts := sorry

/-- A retract of an object of finite injective dimension again has finite injective dimension. -/
theorem HasFiniteInjectiveDimension.ofRetract
    {K L : DerivedCategory C} (r : Retract K L) (hL : HasFiniteInjectiveDimension L) :
    HasFiniteInjectiveDimension K := sorry

end CategoryTheory.DerivedCategory
