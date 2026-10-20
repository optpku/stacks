/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty

/-!
# Equivalence-invariance of algebraic and Deligne-Mumford stacks

Being an algebraic stack or a Deligne-Mumford stack over a scheme is invariant
under equivalence of categories over its big fppf site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicStack

/-- Being an algebraic stack is closed under bicategorical equivalence of
categories fibred in groupoids over `(Sch/S)_fppf`. -/
instance objectProperty.isClosedUnderEquivalences (S : Scheme.{u}) :
    (objectProperty S).IsClosedUnderEquivalences := sorry

/-- An algebraic stack remains an algebraic stack after transport across an
equivalence of categories fibred in groupoids over `(Sch/S)_fppf`. -/
theorem of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y)
    [AlgebraicStack X] : AlgebraicStack Y := sorry

/-- Equivalent categories fibred in groupoids over `(Sch/S)_fppf` are algebraic
stacks simultaneously. -/
theorem iff_of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y) :
    AlgebraicStack X ↔ AlgebraicStack Y := sorry

end AlgebraicStack

namespace DeligneMumfordStack

/-- Being a Deligne-Mumford stack is closed under bicategorical equivalence of
categories fibred in groupoids over `(Sch/S)_fppf`. -/
instance objectProperty.isClosedUnderEquivalences (S : Scheme.{u}) :
    (objectProperty S).IsClosedUnderEquivalences := sorry

/-- A Deligne-Mumford stack remains a Deligne-Mumford stack after transport
across an equivalence of categories fibred in groupoids over `(Sch/S)_fppf`. -/
theorem of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y)
    [DeligneMumfordStack X] : DeligneMumfordStack Y := sorry

/-- Equivalent categories fibred in groupoids over `(Sch/S)_fppf` are
Deligne-Mumford stacks simultaneously. -/
theorem iff_of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y) :
    DeligneMumfordStack X ↔ DeligneMumfordStack Y := sorry

end DeligneMumfordStack

end AlgebraicGeometry

namespace CategoryTheory.BasedCategory

/-- A category over the big fppf site is an algebraic stack when its projection
is fibred in groupoids and the resulting groupoid fibration is an algebraic stack. -/
def IsAlgebraicStack {S : Scheme.{u}} (X : BasedCategory.{u, u + 1} (Over S)) : Prop :=
  ∃ h : Functor.IsFibered.InGroupoids X.p, AlgebraicStack (⟨X, h⟩ : GroupoidsOver S)

/-- A category over the big fppf site is a Deligne-Mumford stack when its projection
is fibred in groupoids and the resulting groupoid fibration is a Deligne-Mumford stack. -/
def IsDeligneMumfordStack {S : Scheme.{u}} (X : BasedCategory.{u, u + 1} (Over S)) : Prop :=
  ∃ h : Functor.IsFibered.InGroupoids X.p, DeligneMumfordStack (⟨X, h⟩ : GroupoidsOver S)

/-- On a category fibred in groupoids, the algebraic-stack predicate agrees with
the algebraic-stack class of the original groupoid fibration. -/
theorem IsAlgebraicStack.toBasedCategory_iff {S : Scheme.{u}} (X : GroupoidsOver S) :
    IsAlgebraicStack X.toBasedCategory ↔ AlgebraicStack X := sorry

/-- On a category fibred in groupoids, the Deligne-Mumford-stack predicate agrees
with the Deligne-Mumford-stack class of the original groupoid fibration. -/
theorem IsDeligneMumfordStack.toBasedCategory_iff {S : Scheme.{u}} (X : GroupoidsOver S) :
    IsDeligneMumfordStack X.toBasedCategory ↔ DeligneMumfordStack X := sorry

/-- Equivalent categories over the big fppf site are algebraic stacks simultaneously. -/
theorem IsAlgebraicStack.iff_of_equivalence {S : Scheme.{u}}
    {X Y : BasedCategory.{u, u + 1} (Over S)} (e : X ≌ Y) :
    IsAlgebraicStack X ↔ IsAlgebraicStack Y := sorry

/-- Equivalent categories over the big fppf site are Deligne-Mumford stacks simultaneously. -/
theorem IsDeligneMumfordStack.iff_of_equivalence {S : Scheme.{u}}
    {X Y : BasedCategory.{u, u + 1} (Over S)} (e : X ≌ Y) :
    IsDeligneMumfordStack X ↔ IsDeligneMumfordStack Y := sorry

end CategoryTheory.BasedCategory
