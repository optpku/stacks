module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Iso
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Direct Summands and Retracts of Computing Derived Values

The computation condition consists of pointwise existence together with an invertible
identity-denominator comparison.  In the situation of Stacks, Situation 05S7 (an exact functor of
triangulated categories and a saturated multiplicative system compatible with the triangulation),
Stacks 05T0 says that each summand of a binary biproduct computing a derived value computes it as
well.  Unlike the definedness statement 05SD (2), no Karoubian hypothesis on the target is needed:
the comparison `RF(X ⊕ Y) = F(X) ⊕ F(Y)` already identifies the summand values.

In a pretriangulated source every retract is a binary-biproduct summand: a split monomorphism
`X ⟶ Y` completes to a distinguished triangle with zero third morphism, which splits (Stacks 05QT,
mathlib `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`).  Hence 05T0 also gives
retract stability of the computing objects, again without any idempotent-completeness assumption.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open CategoryTheory Limits MorphismProperty ObjectProperty Pretriangulated

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation]

section Biproduct

variable {X Y : D}

/-- Stacks 05T0 (1): a right-derived computing binary biproduct has a computing left summand. -/
@[stacks 05T0 "right computation, left summand"]
theorem RightDerived.ComputesAt.left_of_biprod
    (hXY : RightDerived.ComputesAt F S (X ⊞ Y)) :
    RightDerived.ComputesAt F S X := sorry

/-- Stacks 05T0 (2): a right-derived computing binary biproduct has a computing right summand. -/
@[stacks 05T0 "right computation, right summand"]
theorem RightDerived.ComputesAt.right_of_biprod
    (hXY : RightDerived.ComputesAt F S (X ⊞ Y)) :
    RightDerived.ComputesAt F S Y := sorry

/-- Stacks 05T0: if a binary biproduct computes the right-derived value, both summands
compute it. -/
@[stacks 05T0 "right computation on both summands"]
theorem RightDerived.ComputesAt.of_biprod
    (hXY : RightDerived.ComputesAt F S (X ⊞ Y)) :
    RightDerived.ComputesAt F S X ∧ RightDerived.ComputesAt F S Y :=
  ⟨RightDerived.ComputesAt.left_of_biprod F S hXY,
    RightDerived.ComputesAt.right_of_biprod F S hXY⟩

/-- Stacks 05T0 (3): a left-derived computing binary biproduct has a computing left summand. -/
@[stacks 05T0 "left computation, left summand"]
theorem LeftDerived.ComputesAt.left_of_biprod
    (hXY : LeftDerived.ComputesAt F S (X ⊞ Y)) :
    LeftDerived.ComputesAt F S X := sorry

/-- Stacks 05T0 (4): a left-derived computing binary biproduct has a computing right summand. -/
@[stacks 05T0 "left computation, right summand"]
theorem LeftDerived.ComputesAt.right_of_biprod
    (hXY : LeftDerived.ComputesAt F S (X ⊞ Y)) :
    LeftDerived.ComputesAt F S Y := sorry

/-- Stacks 05T0: if a binary biproduct computes the left-derived value, both summands
compute it. -/
@[stacks 05T0 "left computation on both summands"]
theorem LeftDerived.ComputesAt.of_biprod
    (hXY : LeftDerived.ComputesAt F S (X ⊞ Y)) :
    LeftDerived.ComputesAt F S X ∧ LeftDerived.ComputesAt F S Y :=
  ⟨LeftDerived.ComputesAt.left_of_biprod F S hXY,
    LeftDerived.ComputesAt.right_of_biprod F S hXY⟩

end Biproduct

/-- A retract of a right-derived computing object again computes the right-derived value.
The retract is a binary-biproduct summand of the ambient object (Stacks 05QT), so this follows
from Stacks 05T0 and isomorphism invariance (Stacks 05SX). -/
@[stacks 05T0 "right computation of retracts"]
theorem RightDerived.ComputesAt.of_retract {X Y : D} (r : Retract X Y)
    (hY : RightDerived.ComputesAt F S Y) :
    RightDerived.ComputesAt F S X := sorry

/-- A retract of a left-derived computing object again computes the left-derived value.
The retract is a binary-biproduct summand of the ambient object (Stacks 05QT), so this follows
from Stacks 05T0 and isomorphism invariance (Stacks 05SX). -/
@[stacks 05T0 "left computation of retracts"]
theorem LeftDerived.ComputesAt.of_retract {X Y : D} (r : Retract X Y)
    (hY : LeftDerived.ComputesAt F S Y) :
    LeftDerived.ComputesAt F S X := sorry

/-- Objects computing the right-derived value form a retract-stable object property. -/
@[stacks 05T0 "right computation retract stability"]
instance RightDerived.ComputesAt.stableUnderRetracts :
    (RightDerived.ComputesAt.objects F S).IsStableUnderRetracts where
  of_retract r hY := RightDerived.ComputesAt.of_retract F S r hY

/-- Objects computing the left-derived value form a retract-stable object property. -/
@[stacks 05T0 "left computation retract stability"]
instance LeftDerived.ComputesAt.stableUnderRetracts :
    (LeftDerived.ComputesAt.objects F S).IsStableUnderRetracts where
  of_retract r hY := LeftDerived.ComputesAt.of_retract F S r hY

end CategoryTheory.Functor
