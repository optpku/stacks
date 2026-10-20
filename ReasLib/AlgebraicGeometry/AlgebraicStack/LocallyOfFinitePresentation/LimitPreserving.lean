/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Limit preservation and local finite presentation of algebraic-stack morphisms

A morphism of algebraic stacks is limit preserving if and only if it is
limit preserving on objects, if and only if it is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- For a morphism of algebraic stacks, limit preservation, limit preservation
on objects, and local finite presentation are equivalent. -/
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE [Groupoids.Hom.LimitPreserving f,
      Groupoids.Hom.LimitPreservingOnObjects f,
      AlgebraicStack.LocallyOfFinitePresentation f] := sorry

/-- A morphism of algebraic stacks is limit preserving if and only if it is
limit preserving on objects. -/
theorem iff_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.LimitPreserving f ↔
      Groupoids.Hom.LimitPreservingOnObjects f :=
  (tfae f).out 0 1

/-- A morphism of algebraic stacks is limit preserving if and only if it is
locally of finite presentation. -/
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.LimitPreserving f ↔
      AlgebraicStack.LocallyOfFinitePresentation f :=
  (tfae f).out 0 2

/-- A morphism of algebraic stacks that is limit preserving on objects is
locally of finite presentation. -/
instance of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [h : Groupoids.Hom.LimitPreservingOnObjects f] :
    AlgebraicStack.LocallyOfFinitePresentation f :=
  ((tfae f).out 1 2).mp h

/-- A morphism of algebraic stacks that is locally of finite presentation is
limit preserving as a 1-morphism of categories fibred in groupoids. -/
instance homLimitPreserving {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [h : AlgebraicStack.LocallyOfFinitePresentation f] :
    Groupoids.Hom.LimitPreserving f :=
  (iff_locallyOfFinitePresentation f).mpr h

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
