/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-definedness for bounded and unbounded derived functors

Essential constancy of a one-sided bounded object's localization-indexed diagram is independent
of whether the diagram is formed in the bounded or unbounded homotopy category.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- Stacks 05T5: the localization-indexed diagram of a bounded-below object is essentially
constant in the unbounded setting exactly when it is essentially constant in the bounded-below
setting. -/
@[stacks 05T5]
theorem RightDerived.DefinedAt.iff_boundedBelow
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A) :
    RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj ↔
      RightDerived.DefinedAt F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) K := sorry

/-- Stacks 05T5: the localization-indexed diagram of a bounded-above object is essentially
constant in the unbounded setting exactly when it is essentially constant in the bounded-above
setting. -/
@[stacks 05T5]
theorem LeftDerived.DefinedAt.iff_boundedAbove
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A) :
    LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj ↔
      LeftDerived.DefinedAt F.toBoundedAboveDerived
        (HomotopyCategory.Minus.quasiIso A) K := sorry


end CategoryTheory.Functor
