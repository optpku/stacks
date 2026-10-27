/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shift-Vanishing Subcategories of Homological Functors

This leaf owns the object properties cut out by eventual vanishing of the
integer shifts of a functor.  The definitions only require a shifted source;
the pretriangulated and abelian hypotheses enter precisely for the closure
instances.

## Main declarations

* `Functor.oneSidedShiftVanishing` is the direction-neutral primitive.
* `Functor.shiftVanishingPlus`, `Functor.shiftVanishingMinus`, and
  `Functor.shiftVanishingBounded` are the usual one- and two-sided views.
* `Functor.shiftVanishingIn` records an explicit finite shift interval.
-/

open CategoryTheory Limits ObjectProperty Pretriangulated
open scoped ZeroObject

universe vD vA uD uA

namespace CategoryTheory.Functor

/-- The direction in which shifts are required to vanish eventually. -/
@[stacks 05RE]
inductive ShiftVanishingDirection where
  /-- Vanishing on all sufficiently negative shifts. -/
  | negative
  /-- Vanishing on all sufficiently positive shifts. -/
  | positive

section Basic

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- The object property on which the shifts of `H` vanish eventually in a specified direction. -/
@[stacks 05RE]
def oneSidedShiftVanishing (H : D ⥤ A) (direction : ShiftVanishingDirection) :
    ObjectProperty D :=
  fun X ↦
    match direction with
    | .negative => ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧))
    | .positive => ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧))

/-- The source-facing property of objects whose shifted values vanish for all sufficiently
negative shifts. -/
@[stacks 05RE]
def shiftVanishingPlus (H : D ⥤ A) : ObjectProperty D :=
  oneSidedShiftVanishing H .negative

/-- The source-facing property of objects whose shifted values vanish for all sufficiently
positive shifts. -/
@[stacks 05RE]
def shiftVanishingMinus (H : D ⥤ A) : ObjectProperty D :=
  oneSidedShiftVanishing H .positive

/-- The property of objects whose shifted values vanish outside a bounded range. -/
@[stacks 05RE]
def shiftVanishingBounded (H : D ⥤ A) : ObjectProperty D :=
  H.shiftVanishingPlus ⊓ H.shiftVanishingMinus

/-- The scoped category of objects with eventually vanishing negative shifts. -/
scoped[ShiftVanishingSubcategory] notation3:max "D⁺[" H "]" =>
  (Functor.shiftVanishingPlus H).FullSubcategory

/-- The scoped category of objects with eventually vanishing positive shifts. -/
scoped[ShiftVanishingSubcategory] notation3:max "D⁻[" H "]" =>
  (Functor.shiftVanishingMinus H).FullSubcategory

/-- The scoped category of objects with bounded shift support. -/
scoped[ShiftVanishingSubcategory] notation3:max "Dᵇ[" H "]" =>
  (Functor.shiftVanishingBounded H).FullSubcategory

/-- The property of objects whose shifted `H`-values vanish outside `[a, b]`. -/
@[stacks 05RE]
def shiftVanishingIn (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) : ObjectProperty D :=
  fun X ↦ ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X)

/-- The negative-shift formulation of `shiftVanishingPlus`. -/
@[stacks 05RE]
theorem mem_shiftVanishingPlus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingPlus X ↔
      ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧)) := Iff.rfl

/-- The positive-shift formulation of `shiftVanishingMinus`. -/
@[stacks 05RE]
theorem mem_shiftVanishingMinus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingMinus X ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧)) := Iff.rfl

/-- The absolute-value formulation of `shiftVanishingBounded`. -/
@[stacks 05RE]
theorem mem_shiftVanishingBounded_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingBounded X ↔
      ∃ N : ℕ, ∀ n : ℤ, N ≤ Int.natAbs n → IsZero (H.obj (X⟦n⟧)) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a.natAbs + b.natAbs, ?_⟩
    intro n hn
    have ha' : -(a.natAbs : ℤ) ≤ a := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le a
    have hb' : b ≤ (b.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self b
    by_cases h : 0 ≤ n
    · have hn' : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg h
      exact hb n (by omega)
    · have hn' : (n.natAbs : ℤ) = -n := by
        rw [Int.natCast_natAbs, abs_of_neg (by omega)]
      exact ha n (by omega)
  · rintro ⟨N, hN⟩
    constructor
    · refine ⟨-(N : ℤ), fun n hn ↦ hN n ?_⟩
      have hn' : (n.natAbs : ℤ) = -n := by
        rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
      omega
    · refine ⟨(N : ℤ), fun n hn ↦ hN n ?_⟩
      have hn' : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg (by omega)
      omega

/-- The explicit-interval formulation of `shiftVanishingIn`. -/
@[stacks 05RE]
theorem mem_shiftVanishingIn_iff (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) (X : D) :
    H.shiftVanishingIn a b X ↔
      ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X) := Iff.rfl

namespace shiftVanishingPlus

/-- Eventual negative-shift vanishing is stable under retracts. -/
@[stacks 05RE]
instance isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingPlus.IsStableUnderRetracts where
  of_retract r hY := by
    obtain ⟨N, hN⟩ := hY
    refine ⟨N, fun n hn ↦ ?_⟩
    exact IsZero.of_mono (r.map (shiftFunctor D n ⋙ H)).i (hN n hn)

end shiftVanishingPlus

namespace shiftVanishingMinus

/-- Eventual positive-shift vanishing is stable under retracts. -/
@[stacks 05RE]
instance isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingMinus.IsStableUnderRetracts where
  of_retract r hY := by
    obtain ⟨N, hN⟩ := hY
    refine ⟨N, fun n hn ↦ ?_⟩
    exact IsZero.of_mono (r.map (shiftFunctor D n ⋙ H)).i (hN n hn)

end shiftVanishingMinus

namespace shiftVanishingBounded

/-- Bounded shift vanishing is stable under retracts. -/
@[stacks 05RE]
instance isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingBounded.IsStableUnderRetracts where
  of_retract r hY :=
    ⟨H.shiftVanishingPlus.prop_of_retract r hY.1,
      H.shiftVanishingMinus.prop_of_retract r hY.2⟩

end shiftVanishingBounded

end Basic

section Triangulated

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

namespace shiftVanishingPlus

/-- The negative shift-vanishing property is triangulated for a homological functor. -/
@[stacks 05RE]
instance isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingPlus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero D, 0,
    fun n _ ↦ (shiftFunctor D n ⋙ H).map_isZero (isZero_zero D)⟩
  toIsStableUnderShift := ⟨fun a ↦ ⟨by
    rintro X ⟨N, hN⟩
    refine ⟨N - a, ?_⟩
    intro n hn
    exact (hN (a + n) (by omega)).of_iso
      (H.mapIso ((shiftFunctorAdd D a n).app X).symm)⟩⟩
  toIsTriangulatedClosed₂ := .mk' (by
    rintro T hT ⟨N₁, h₁⟩ ⟨N₃, h₃⟩
    refine ⟨min N₁ N₃, ?_⟩
    intro n hn
    exact (H.map_distinguished_exact _
      (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
        ((h₁ n (hn.trans (min_le_left _ _))).eq_of_src _ _)
        ((h₃ n (hn.trans (min_le_right _ _))).eq_of_tgt _ _))

end shiftVanishingPlus

namespace shiftVanishingMinus

/-- The positive shift-vanishing property is triangulated for a homological functor. -/
@[stacks 05RE]
instance isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingMinus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero D, 0,
    fun n _ ↦ (shiftFunctor D n ⋙ H).map_isZero (isZero_zero D)⟩
  toIsStableUnderShift := ⟨fun a ↦ ⟨by
    rintro X ⟨N, hN⟩
    refine ⟨N - a, ?_⟩
    intro n hn
    exact (hN (a + n) (by omega)).of_iso
      (H.mapIso ((shiftFunctorAdd D a n).app X).symm)⟩⟩
  toIsTriangulatedClosed₂ := .mk' (by
    rintro T hT ⟨N₁, h₁⟩ ⟨N₃, h₃⟩
    refine ⟨max N₁ N₃, ?_⟩
    intro n hn
    exact (H.map_distinguished_exact _
      (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
        ((h₁ n ((le_max_left _ _).trans hn)).eq_of_src _ _)
        ((h₃ n ((le_max_right _ _).trans hn)).eq_of_tgt _ _))

end shiftVanishingMinus

namespace shiftVanishingBounded

/-- The bounded shift-vanishing property is triangulated for a homological functor. -/
@[stacks 05RE]
instance isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingBounded.IsTriangulated := by
  change (H.shiftVanishingPlus ⊓ H.shiftVanishingMinus).IsTriangulated
  infer_instance

end shiftVanishingBounded

end Triangulated

end CategoryTheory.Functor
