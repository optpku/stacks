/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Extension.Interval
public import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing

@[expose] public section

/-!
# Finite Intervals for Shift Vanishing

This leaf records the order, translation, and closure API for the exact
shift-vanishing property of a functor.  It is independent of additive
extension stages.
-/

open CategoryTheory Limits ObjectProperty Pretriangulated
open scoped ZeroObject

universe vD vA uD uA

namespace CategoryTheory.Functor.shiftVanishingIn

section Basic

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- Every finite shift interval gives bounded shift vanishing. -/
@[stacks 05RE "finite interval implies bounded vanishing"]
theorem le_bounded (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) :
    H.shiftVanishingIn a b ≤ H.shiftVanishingBounded := sorry

/-- Enlarging the allowed interval preserves exact shift vanishing. -/
theorem mono (H : D ⥤ A) [H.ShiftSequence ℤ]
    {l u l' u' : ℤ} (hl : l' ≤ l) (hu : u ≤ u') :
    H.shiftVanishingIn l u ≤ H.shiftVanishingIn l' u' := sorry

/-- Vanishing of a shifted object translates to the corresponding interval on the object. -/
theorem of_shift (H : D ⥤ A) [H.ShiftSequence ℤ]
    {X : D} {a b k : ℤ} (hX : H.shiftVanishingIn a b (X⟦k⟧)) :
    H.shiftVanishingIn (a + k) (b + k) X := sorry

/-- Exact shift vanishing is stable under retracts. -/
instance isStableUnderRetracts (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) :
    (H.shiftVanishingIn a b).IsStableUnderRetracts := sorry

/-- Shifting generators through `[c, d]` translates their common vanishing interval by
the same endpoints. -/
@[stacks 0FX8]
theorem shiftInterval_le (H : D ⥤ A) [H.ShiftSequence ℤ]
    (E : ObjectProperty D) (a b c d : ℤ)
    (hE : E ≤ H.shiftVanishingIn a b) :
    E[c, d] ≤ H.shiftVanishingIn (a + c) (b + d) := sorry

end Basic

section Triangulated

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- Exact shift vanishing contains every zero object. -/
instance containsZero (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    (a b : ℤ) :
    (H.shiftVanishingIn a b).ContainsZero := sorry

/-- Exact shift vanishing is closed under middle terms of distinguished triangles. -/
instance isTriangulatedClosed₂ (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    (a b : ℤ) :
    (H.shiftVanishingIn a b).IsTriangulatedClosed₂ := sorry

/-- Exact shift vanishing is closed under binary coproducts. -/
instance isClosedUnderBinaryCoproducts
    (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ] (a b : ℤ) :
    (H.shiftVanishingIn a b).IsClosedUnderBinaryCoproducts := sorry

/-- Exact shift vanishing is closed under finite coproducts. -/
instance isClosedUnderFiniteCoproducts
    (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ] (a b : ℤ) :
    (H.shiftVanishingIn a b).IsClosedUnderFiniteCoproducts := sorry

end Triangulated

end CategoryTheory.Functor.shiftVanishingIn

namespace CategoryTheory.Functor.shiftVanishingBounded

section

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- Bounded shift vanishing is equivalent to vanishing outside some finite interval. -/
@[stacks 05RE "bounded vanishing interval characterization"]
theorem mem_iff_exists_interval (H : D ⥤ A) [H.ShiftSequence ℤ] (X : D) :
    H.shiftVanishingBounded X ↔ ∃ a b : ℤ, H.shiftVanishingIn a b X := sorry

end

end CategoryTheory.Functor.shiftVanishingBounded
