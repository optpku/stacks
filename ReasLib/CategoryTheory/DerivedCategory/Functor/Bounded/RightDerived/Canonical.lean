/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Existence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Comparison
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Canonical Bounded-Below Right Derived Functor

This file specializes the total right-derived construction to bounded-below homotopy and derived
categories.  It also owns the resolution-independent degreewise vanishing condition used by
finite-cohomological-dimension arguments.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive]

/-- Enough bounded right-acyclic objects canonically provide the bounded-below right derived
functor required by the degree API. -/
@[stacks 05TA]
theorem hasDerived
    [(Functor.RightAcyclic.Bounded F).HasMonoEmbedding] :
    F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) := by
  let hEverywhere :
      Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) :=
    Functor.RightAcyclic.Bounded.everywhereDefined F
  let hPointwise :
      F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso A) :=
    @Functor.RightDerived.EverywhereDefined.hasPointwise _ _ _ _ _ _
      hEverywhere
  exact @Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
    _ _ _ _ _ _ hPointwise

/-- The canonical bounded-below right derived functor of `F`. -/
@[stacks 015A]
abbrev functor
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  F.toBoundedBelowDerived.totalRightDerived
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
    (HomotopyCategory.Plus.quasiIso A)

/-- The canonical localization unit of the bounded-below right derived
functor. -/
@[stacks 015A]
noncomputable abbrev unit
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    F.toBoundedBelowDerived ⟶
      (DerivedCategory.Plus.Qh :
        HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A) ⋙ functor F :=
  F.toBoundedBelowDerived.totalRightDerivedUnit
    (DerivedCategory.Plus.Qh :
      HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
    (HomotopyCategory.Plus.quasiIso A)

/-- The degree-`i` functor of the canonical bounded-below right derived functor. -/
@[stacks 015A]
abbrev degree
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (i : ℤ) : A ⥤ B :=
  RightDerived.degree (functor F) i

/-- The canonical comparison from the underived functor to the zeroth right
derived functor. -/
@[stacks 015A]
noncomputable abbrev zero
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    F ⟶ degree F 0 :=
  RightDerived.zero F (functor F) (unit F)

namespace Vanishes

/-- The canonical bounded-below right derived functor vanishes in degree `n`. -/
@[stacks 07K7]
abbrev inDegree
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℕ) : Prop :=
  IsZero (degree F n)

/-- Degreewise vanishing of the bounded-below right derived functor is equivalent to objectwise
vanishing. -/
@[stacks 07K7]
theorem inDegree_iff
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℕ) :
    inDegree F n ↔ ∀ X : A, IsZero ((degree F n).obj X) := sorry

end Vanishes


end CategoryTheory.Functor.RightDerived.Bounded
