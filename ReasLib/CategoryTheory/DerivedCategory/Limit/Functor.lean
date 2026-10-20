/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle

@[expose] public section

/-!
# Functors Preserving Derived Limits

@stack 0CQD
@stack 08U1

This module records preservation of Milnor derived limits by the canonical total right derived
functor of an additive functor.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w wA wB u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace Functor.RightDerived.KInjective

section

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Abelian A]
variable [Category.{v₂} B] [Abelian B]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wB} B]

/-- The canonical total right derived functor of an additive functor carries derived-limit data
for a sequential inverse system to a derived limit for its image. -/
@[stacks 0CQD, stacks 08U1]
theorem preservesDerivedLimit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {Ksys : SequentialInverseSystem (DerivedCategory A)} {K : DerivedCategory A}
    (hK : IsDerivedLimit Ksys K) :
    Nonempty
      (IsDerivedLimit
        (Ksys ⋙ functor F)
        ((functor F).obj K)) := sorry

end

end Functor.RightDerived.KInjective

end CategoryTheory
