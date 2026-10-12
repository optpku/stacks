/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Iso
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Retracts
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retracts of Computing Derived Values

The computation condition consists of pointwise existence together with an invertible
identity-denominator comparison.  This leaf gives that stronger object property its Karoubian
retract API and derives the binary-biproduct summand lemmas from the generic object-property
retract interface.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open CategoryTheory Limits ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]

/-- Stacks 05T0: in an idempotent-complete target, objects computing the right-derived value form
a retract-stable object property. -/
@[stacks 05T0 "right computation retract stability"]
instance RightDerived.ComputesAt.stableUnderRetracts
    [IsIdempotentComplete D'] :
    (RightDerived.ComputesAt.objects F S).IsStableUnderRetracts := sorry

/-- Stacks 05T0: in an idempotent-complete target, objects computing the left-derived value form
a retract-stable object property. -/
@[stacks 05T0 "left computation retract stability"]
instance LeftDerived.ComputesAt.stableUnderRetracts
    [IsIdempotentComplete D'] :
    (LeftDerived.ComputesAt.objects F S).IsStableUnderRetracts := sorry

/-- A retract of a right-derived computing object again computes the right-derived value. -/
theorem RightDerived.ComputesAt.of_retract
    [IsIdempotentComplete D'] {X Y : D} (r : Retract X Y)
    (hY : RightDerived.ComputesAt F S Y) :
    RightDerived.ComputesAt F S X := sorry

/-- A retract of a left-derived computing object again computes the left-derived value. -/
theorem LeftDerived.ComputesAt.of_retract
    [IsIdempotentComplete D'] {X Y : D} (r : Retract X Y)
    (hY : LeftDerived.ComputesAt F S Y) :
    LeftDerived.ComputesAt F S X := sorry

section Biproduct

variable [HasZeroMorphisms D] {X Y : D} [HasBinaryBiproduct X Y]

/-- Stacks 05T0 (1): a right-derived computing binary biproduct has a computing left summand. -/
@[stacks 05T0 "right computation, left summand"]
theorem RightDerived.ComputesAt.left_of_biprod
    [(RightDerived.ComputesAt.objects F S).IsStableUnderRetracts]
    (hXY : RightDerived.ComputesAt F S (X ⊞ Y)) :
    RightDerived.ComputesAt F S X := sorry

/-- Stacks 05T0 (2): a right-derived computing binary biproduct has a computing right summand. -/
@[stacks 05T0 "right computation, right summand"]
theorem RightDerived.ComputesAt.right_of_biprod
    [(RightDerived.ComputesAt.objects F S).IsStableUnderRetracts]
    (hXY : RightDerived.ComputesAt F S (X ⊞ Y)) :
    RightDerived.ComputesAt F S Y := sorry

/-- If a binary biproduct computes the right-derived value, both summands compute it. -/
theorem RightDerived.ComputesAt.of_biprod
    [(RightDerived.ComputesAt.objects F S).IsStableUnderRetracts]
    (hXY : RightDerived.ComputesAt F S (X ⊞ Y)) :
    RightDerived.ComputesAt F S X ∧ RightDerived.ComputesAt F S Y := sorry

/-- Stacks 05T0 (3): a left-derived computing binary biproduct has a computing left summand. -/
@[stacks 05T0 "left computation, left summand"]
theorem LeftDerived.ComputesAt.left_of_biprod
    [(LeftDerived.ComputesAt.objects F S).IsStableUnderRetracts]
    (hXY : LeftDerived.ComputesAt F S (X ⊞ Y)) :
    LeftDerived.ComputesAt F S X := sorry

/-- Stacks 05T0 (4): a left-derived computing binary biproduct has a computing right summand. -/
@[stacks 05T0 "left computation, right summand"]
theorem LeftDerived.ComputesAt.right_of_biprod
    [(LeftDerived.ComputesAt.objects F S).IsStableUnderRetracts]
    (hXY : LeftDerived.ComputesAt F S (X ⊞ Y)) :
    LeftDerived.ComputesAt F S Y := sorry

/-- If a binary biproduct computes the left-derived value, both summands compute it. -/
theorem LeftDerived.ComputesAt.of_biprod
    [(LeftDerived.ComputesAt.objects F S).IsStableUnderRetracts]
    (hXY : LeftDerived.ComputesAt F S (X ⊞ Y)) :
    LeftDerived.ComputesAt F S X ∧ LeftDerived.ComputesAt F S Y := sorry

end Biproduct

end CategoryTheory.Functor
