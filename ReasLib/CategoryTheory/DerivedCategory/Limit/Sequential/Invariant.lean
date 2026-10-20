/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Pro

@[expose] public section

/-!
# Pro-Invariance of Sequential Derived Limit

This module isolates the reusable property that a derived inverse-limit model
sends stagewise pro-isomorphisms to isomorphisms.
@stack 091B
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Pro

/-- A model in which total right derived sequential inverse limit is invariant
under stagewise pro-isomorphisms. -/
@[stacks 091B]
class Invariant (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
    [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : SequentialInverseSystem A ⥤ A).Additive]
    [HasDerivedFunctor A] : Prop where
  /-- Derived inverse limit inverts the stagewise pro-isomorphism property. -/
  isInvertedBy : (isomorphisms A).IsInvertedBy (functor A)

/-- Lemma 15.87.13 (091B), in abstract model form: a stagewise pro-isomorphism is sent to an
isomorphism by a pro-invariant sequential derived-limit model. -/
@[stacks 091B]
theorem map_isIso
    [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
    [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : SequentialInverseSystem A ⥤ A).Additive]
    [HasDerivedFunctor A] [Invariant A]
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L)
    (hf : isomorphisms A f) :
    _root_.CategoryTheory.IsIso ((functor A).map f) := sorry

end Pro

end CategoryTheory.DerivedLimit
