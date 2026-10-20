module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Iso
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shift Closure for Computing Pointwise Derived Values

For a shift-compatible localization class and a shift-compatible functor, this leaf upgrades the
shift transport of raw pointwise derived values to the assertion that an object computes that
value.  It is independent of any particular derived-category model.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]

/-- Stacks 05SY: the objects computing the pointwise right-derived value of `F` are stable
under integer shifts. -/
@[stacks 05SY]
instance Functor.RightDerived.ComputesAt.stableUnderShift
    [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ] :
    IsStableUnderShift (Functor.RightDerived.ComputesAt.objects F S) ℤ := sorry

/-- Stacks 05SY: the objects computing the pointwise left-derived value of `F` are stable
under integer shifts. -/
@[stacks 05SY]
instance Functor.LeftDerived.ComputesAt.stableUnderShift
    [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ] :
    IsStableUnderShift (Functor.LeftDerived.ComputesAt.objects F S) ℤ := sorry

/-- Stacks 05SY: a pointwise right-derived value is computed at `X` exactly when it is computed
at `X⟦n⟧`. -/
@[stacks 05SY]
theorem Functor.RightDerived.ComputesAt.iff_shift
    [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    (X : D) (n : ℤ) :
    Functor.RightDerived.ComputesAt F S X ↔ Functor.RightDerived.ComputesAt F S (X⟦n⟧) := by
  simpa only [Functor.RightDerived.ComputesAt.objects] using
    ((Functor.RightDerived.ComputesAt.objects F S).prop_shift_iff_of_isStableUnderShift X n).symm

/-- Stacks 05SY: a pointwise left-derived value is computed at `X` exactly when it is computed
at `X⟦n⟧`. -/
@[stacks 05SY]
theorem Functor.LeftDerived.ComputesAt.iff_shift
    [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    (X : D) (n : ℤ) :
    Functor.LeftDerived.ComputesAt F S X ↔ Functor.LeftDerived.ComputesAt F S (X⟦n⟧) := by
  simpa only [Functor.LeftDerived.ComputesAt.objects] using
    ((Functor.LeftDerived.ComputesAt.objects F S).prop_shift_iff_of_isStableUnderShift X n).symm

/-- A right-derived computation condition transports forward through a shift without requiring a
local instance declaration. -/
@[stacks 05SY]
theorem Functor.RightDerived.ComputesAt.shift
    [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    {X : D} (n : ℤ) (hX : Functor.RightDerived.ComputesAt F S X) :
    Functor.RightDerived.ComputesAt F S (X⟦n⟧) :=
  (Functor.RightDerived.ComputesAt.iff_shift F S X n).mp hX

/-- A left-derived computation condition transports forward through a shift without requiring a
local instance declaration. -/
@[stacks 05SY]
theorem Functor.LeftDerived.ComputesAt.shift
    [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    {X : D} (n : ℤ) (hX : Functor.LeftDerived.ComputesAt F S X) :
    Functor.LeftDerived.ComputesAt F S (X⟦n⟧) :=
  (Functor.LeftDerived.ComputesAt.iff_shift F S X n).mp hX

end CategoryTheory
