/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Preservation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Right Derived Functors Preserve Homotopy Limits

This leaf specializes the neutral homotopy-limit preservation API to the
canonical total right derived functor of an additive functor.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor.RightDerived.KInjective

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Abelian A]
variable [Category.{v₂} B] [Abelian B]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wB} B]

/-- Lemma 19.13.6 (Stacks 08U1): the canonical total right derived functor of an additive
functor preserves sequential homotopy limits when the source is Grothendieck and the target has
exact countable products. -/
@[stacks 08U1]
theorem preservesHomotopyLimit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {Ksys : SequentialInverseSystem (DerivedCategory A)} {K : DerivedCategory A}
    (hK : HomotopyLimit.IsOf Ksys K) :
    HomotopyLimit.IsOf (Ksys ⋙ functor F) ((functor F).obj K) := sorry

end CategoryTheory.Functor.RightDerived.KInjective
