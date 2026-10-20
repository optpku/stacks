/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Basic
public import ReasLib.CategoryTheory.Functor.Derived.AcyclicClass.BoundedAbove
public import ReasLib.CategoryTheory.Functor.Derived.AcyclicClass.BoundedBelow
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Global Bounded Derived Functors from Acyclic Objects

This leaf specializes the property-neutral acyclic-class globalization to the canonical
right-acyclic and left-acyclic object properties of a bounded derived functor. It owns the
source-level everywhere-defined conclusions and their pointwise/total Mathlib consequences.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- Stacks 05TA: bounded-below right-acyclic objects form the canonical bounded-below
acyclic class for an additive functor. -/
@[stacks 05TA]
instance RightAcyclic.Bounded.isAcyclicClass :
    F.IsBoundedBelowAcyclicClass (RightAcyclic.Bounded F) := sorry

/-- Stacks 05TA: bounded-above left-acyclic objects form the canonical bounded-above
acyclic class for an additive functor. -/
@[stacks 05TA]
instance LeftAcyclic.Bounded.isAcyclicClass :
    F.IsBoundedAboveAcyclicClass (LeftAcyclic.Bounded F) := sorry

/-- Stacks 05TA: the zero object is bounded-below right-acyclic. -/
@[stacks 05TA]
noncomputable instance RightAcyclic.Bounded.containsZero :
    (RightAcyclic.Bounded F).ContainsZero := sorry

/-- Stacks 05TA: the zero object is bounded-above left-acyclic. -/
@[stacks 05TA]
noncomputable instance LeftAcyclic.Bounded.containsZero :
    (LeftAcyclic.Bounded F).ContainsZero := sorry

section Right

/-- Stacks 05TA (1): the canonical bounded-below right-acyclic class supplies source-definedness
at every bounded-below homotopy object. -/
@[stacks 05TA "canonical source-definedness instance"]
noncomputable instance RightAcyclic.Bounded.everywhereDefined
    [(RightAcyclic.Bounded F).HasMonoEmbedding] :
    Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Stacks 05TA (1): enough bounded-below right-acyclic objects give Mathlib's pointwise
bounded-below right-derived functor. -/
@[stacks 05TA]
theorem RightAcyclic.Bounded.hasPointwiseDerived
    [(RightAcyclic.Bounded F).HasMonoEmbedding] :
    F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Stacks 05TA (1): enough bounded-below right-acyclic objects give the total bounded-below
right-derived functor. -/
@[stacks 05TA]
theorem RightAcyclic.Bounded.hasDerived
    [(RightAcyclic.Bounded F).HasMonoEmbedding] :
    F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Stacks 05TA (1): a termwise bounded-below right-acyclic complex computes the bounded-below
right-derived value. -/
@[stacks 05TA]
theorem RightAcyclic.Bounded.computesAt_of_termwise
    [(RightAcyclic.Bounded F).HasMonoEmbedding]
    (K : HomotopyCategory.Plus A)
    (hK : RightAcyclic.Bounded.Termwise F K) :
    RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K := sorry

end Right

section Left

/-- Stacks 05TA (2): the canonical bounded-above left-acyclic class supplies source-definedness
at every bounded-above homotopy object. -/
@[stacks 05TA "canonical source-definedness instance"]
noncomputable instance LeftAcyclic.Bounded.everywhereDefined
    [(LeftAcyclic.Bounded F).HasEpiCover] :
    Functor.LeftDerived.EverywhereDefined F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) := sorry

/-- Stacks 05TA (2): enough bounded-above left-acyclic objects give Mathlib's pointwise
bounded-above left-derived functor. -/
@[stacks 05TA]
theorem LeftAcyclic.Bounded.hasPointwiseDerived
    [(LeftAcyclic.Bounded F).HasEpiCover] :
    F.toBoundedAboveDerived.HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A) := sorry

/-- Stacks 05TA (2): enough bounded-above left-acyclic objects give the total bounded-above
left-derived functor. -/
@[stacks 05TA]
theorem LeftAcyclic.Bounded.hasDerived
    [(LeftAcyclic.Bounded F).HasEpiCover] :
    F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A) := sorry

/-- Stacks 05TA (2): a termwise bounded-above left-acyclic complex computes the bounded-above
left-derived value. -/
@[stacks 05TA]
theorem LeftAcyclic.Bounded.computesAt_of_termwise
    [(LeftAcyclic.Bounded F).HasEpiCover]
    (K : HomotopyCategory.Minus A)
    (hK : LeftAcyclic.Bounded.Termwise F K) :
    LeftDerived.ComputesAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K := sorry

end Left


end CategoryTheory.Functor
