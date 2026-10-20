/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Invariant

@[expose] public section

/-!
# Sequential Derived Limits in Grothendieck Abelian Categories

This leaf constructs the standard stagewise pro-invariant derived-limit model
under Grothendieck and exact-countable-product hypotheses.
@stack 07KX
@stack 0CQD
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w wA wSys u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- Lemma 15.87.9 (07KX), in Grothendieck-category form: total right derived inverse limit is
a derived limit of the stagewise evaluation tower. -/
@[stacks 07KX, stacks 0CQD, stacks 08U1 "stagewise inverse-limit model"]
theorem isDerivedLimit_of_tower
    [IsGrothendieckAbelian.{w} A]
    [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasCountableProducts A] [CountableAB4Star A]
    [PreservesLimitsOfShape (Discrete ℕ) (lim : SequentialInverseSystem A ⥤ A)]
    (K : DerivedCategory (SequentialInverseSystem A)) :
    Nonempty (IsDerivedLimit (Stage.tower K) ((functor A).obj K)) := sorry

namespace Pro.Invariant

/-- Grothendieck hypotheses provide the standard stagewise
pro-isomorphism-invariant model of derived sequential inverse limit. -/
@[stacks 07KX, stacks 0CQD, stacks 08U1 "Grothendieck model for derived sequential limits"]
instance ofGrothendieck
    [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : SequentialInverseSystem A ⥤ A).Additive]
    [HasDerivedFunctor A]
    [IsGrothendieckAbelian.{w} A]
    [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]
    [HasCountableProducts A] [CountableAB4Star A]
    [PreservesLimitsOfShape (Discrete ℕ) (lim : SequentialInverseSystem A ⥤ A)] :
    Pro.Invariant A := sorry

end Pro.Invariant

end CategoryTheory.DerivedLimit
