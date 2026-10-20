/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude

/-!
# Shifts and injective amplitude

Cohomological shift translates both endpoints of injective amplitude.  Consequently finite
injective dimension is a shift-stable object property.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Shifting a derived object translates both endpoints of its injective-amplitude interval. -/
theorem hasInjectiveAmplitudeIn_shift_iff
    (K : DerivedCategory C) (n a b : ℤ) :
    HasInjectiveAmplitudeIn (K⟦n⟧) a b ↔
      HasInjectiveAmplitudeIn K (a + n) (b + n) := sorry

/-- Finite injective dimension is invariant under cohomological shift. -/
theorem hasFiniteInjectiveDimension_shift_iff (K : DerivedCategory C) (n : ℤ) :
    HasFiniteInjectiveDimension (K⟦n⟧) ↔ HasFiniteInjectiveDimension K := sorry

/-- Finite injective dimension is stable under all integral shifts. -/
instance finiteInjectiveDimension_isStableUnderShift :
    (finiteInjectiveDimension (C := C)).IsStableUnderShift ℤ := sorry

end CategoryTheory.DerivedCategory
