/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Monomorphism
import StacksCheckRecall

/-!
# Monomorphisms induce injective maps of points

A monomorphism of algebraic stacks induces an injective map of sets of
points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 100.8.5: a monomorphism of algebraic stacks induces an injective map of
sets of points. -/
@[stacks 0500] #check (AlgebraicGeometry.AlgebraicStack.Points.map_injective_of_mono :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Mono f],
    Function.Injective (AlgebraicGeometry.AlgebraicStack.Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Equivalent.map_iff_of_mono :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    {p q : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X}
    (f : X ⟶ Y) [Groupoids.Hom.Mono f],
    AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Equivalent (p.map f) (q.map f) ↔
      AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Equivalent p q)
