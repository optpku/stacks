/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Properties

/-!
# Vanishing characterizations of left-acyclic objects

This file is the left-derived companion to the right-acyclic characterization API.  For a
bounded-above model it uses negative cohomological degrees, while Mathlib's projective-resolution
derived functors use positive homological degrees indexed by `ℕ`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section BoundedAboveVanishes

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Stacks 015C: all strictly negative cohomological degrees of a bounded-above left-derived
model vanish on `X`. -/
@[stacks 015C "bounded left-derived negative-degree vanishing"]
abbrev LeftDerived.Bounded.Vanishes.belowZero
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (X : A) : Prop :=
  ∀ ⦃i : ℤ⦄, i < 0 → IsZero ((LeftDerived.degree LF i).obj X)

end BoundedAboveVanishes

section BoundedAbove

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  [(𝟭 A).toBoundedAboveDerived.IsLocalization
    (HomotopyCategory.Minus.quasiIso A)]
  (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
  (ε : DerivedCategory.Minus.Qh A ⋙ LF ⟶ F.toBoundedAboveDerived)
  [LF.IsLeftDerivedFunctor ε (HomotopyCategory.Minus.quasiIso A)]

/-- Stacks 015C: an object is bounded-above left acyclic exactly when its degree-zero comparison
is invertible and every negative cohomological degree vanishes. -/
@[stacks 015C "bounded left-acyclic vanishing characterization"]
theorem LeftAcyclic.Bounded.iff_zero_and_vanishes (X : A) :
    LeftAcyclic.Bounded F X ↔
      IsIso ((LeftDerived.zero F LF ε).app X) ∧
        LeftDerived.Bounded.Vanishes.belowZero LF X := sorry

/-- Stacks 015C: for a right exact additive functor, bounded-above left acyclicity is exactly
negative-degree left-derived vanishing. -/
@[stacks 015C "right-exact bounded left-acyclic vanishing characterization"]
theorem LeftAcyclic.Bounded.iff_vanishes [PreservesFiniteColimits F] (X : A) :
    LeftAcyclic.Bounded F X ↔
      LeftDerived.Bounded.Vanishes.belowZero LF X := sorry

end BoundedAbove

section ProjectiveResolutionVanishes

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasProjectiveResolutions A]

/-- Stacks 015C: all strictly positive ordinary left-derived degrees of `F` vanish on `X`. -/
@[stacks 015C "ordinary left-derived positive-degree vanishing"]
abbrev LeftDerived.Vanishes.aboveZero (F : A ⥤ B) [F.Additive] (X : A) : Prop :=
  ∀ n : ℕ, IsZero ((F.leftDerived (n + 1)).obj X)

end ProjectiveResolutionVanishes

section Unbounded

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [HasProjectiveResolutions A]

/-- Stacks 015C: ordinary left acyclicity is characterized by the degree-zero comparison and
vanishing of all positive homological left-derived degrees. -/
@[stacks 015C "ordinary left-acyclic vanishing characterization"]
theorem LeftAcyclic.iff_zero_and_vanishes
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (X : A) :
    LeftAcyclic F X ↔
      IsIso (F.fromLeftDerivedZero.app X) ∧ LeftDerived.Vanishes.aboveZero F X := sorry

/-- Stacks 015C: for a right exact additive functor, ordinary left acyclicity is exactly
positive-degree left-derived vanishing. -/
@[stacks 015C "right-exact ordinary left-acyclic vanishing characterization"]
theorem LeftAcyclic.iff_vanishes
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [PreservesFiniteColimits F] (X : A) :
    LeftAcyclic F X ↔ LeftDerived.Vanishes.aboveZero F X := sorry

end Unbounded

end CategoryTheory.Functor
