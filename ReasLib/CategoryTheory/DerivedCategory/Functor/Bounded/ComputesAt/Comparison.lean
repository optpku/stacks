/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Comparison
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computing objects for bounded and unbounded derived functors

At a one-sided bounded homotopy object, the identity denominator computes the derived value in
the bounded setting exactly when it does so in the unbounded setting.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- Stacks 05T5: a bounded-below homotopy object computes the pointwise right-derived functor in
the unbounded setting exactly when it computes the bounded-below derived functor. -/
@[stacks 05T5]
theorem RightDerived.ComputesAt.iff_boundedBelow
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A) :
    RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj ↔
      RightDerived.ComputesAt F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) K := sorry

/-- Stacks 05T5: a bounded-above homotopy object computes the pointwise left-derived functor in
the unbounded setting exactly when it computes the bounded-above derived functor. -/
@[stacks 05T5]
theorem LeftDerived.ComputesAt.iff_boundedAbove
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A) :
    LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj ↔
      LeftDerived.ComputesAt F.toBoundedAboveDerived
        (HomotopyCategory.Minus.quasiIso A) K := sorry


end CategoryTheory.Functor
