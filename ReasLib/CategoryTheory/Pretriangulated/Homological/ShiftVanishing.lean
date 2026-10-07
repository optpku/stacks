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
      ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧)) := sorry

/-- The positive-shift formulation of `shiftVanishingMinus`. -/
@[stacks 05RE]
theorem mem_shiftVanishingMinus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingMinus X ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧)) := sorry

/-- The absolute-value formulation of `shiftVanishingBounded`. -/
@[stacks 05RE]
theorem mem_shiftVanishingBounded_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingBounded X ↔
      ∃ N : ℕ, ∀ n : ℤ, N ≤ Int.natAbs n → IsZero (H.obj (X⟦n⟧)) := sorry

/-- The explicit-interval formulation of `shiftVanishingIn`. -/
@[stacks 05RE]
theorem mem_shiftVanishingIn_iff (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) (X : D) :
    H.shiftVanishingIn a b X ↔
      ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X) := sorry

namespace shiftVanishingPlus

/-- Eventual negative-shift vanishing is stable under retracts. -/
@[stacks 05RE]
instance isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingPlus.IsStableUnderRetracts := sorry

end shiftVanishingPlus

namespace shiftVanishingMinus

/-- Eventual positive-shift vanishing is stable under retracts. -/
@[stacks 05RE]
instance isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingMinus.IsStableUnderRetracts := sorry

end shiftVanishingMinus

namespace shiftVanishingBounded

/-- Bounded shift vanishing is stable under retracts. -/
@[stacks 05RE]
instance isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingBounded.IsStableUnderRetracts := sorry

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
    H.shiftVanishingPlus.IsTriangulated := sorry

end shiftVanishingPlus

namespace shiftVanishingMinus

/-- The positive shift-vanishing property is triangulated for a homological functor. -/
@[stacks 05RE]
instance isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingMinus.IsTriangulated := sorry

end shiftVanishingMinus

namespace shiftVanishingBounded

/-- The bounded shift-vanishing property is triangulated for a homological functor. -/
@[stacks 05RE]
instance isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingBounded.IsTriangulated := sorry

end shiftVanishingBounded

end Triangulated

end CategoryTheory.Functor
