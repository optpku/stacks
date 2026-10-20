/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Lifting
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.Points
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.14.6: A universally injective morphism of algebraic stacks lifts
an algebraically closed field-valued point in its image over the same field,
up to a 2-isomorphism. -/
@[stacks 0DTM] #check
  (AlgebraicGeometry.AlgebraicStack.UniversallyInjective.exists_algClosed_lift :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} [AlgebraicStack.UniversallyInjective f]
    {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y),
    AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of k σ y) ∈
      Set.range (AlgebraicStack.Points.map f) →
    ∃ x : GroupoidsOver.slice (Over.mk σ) ⟶ X, Nonempty (x ≫ f ≅ y))

#check (AlgebraicGeometry.AlgebraicStack.UniversallyInjective.exists_algClosed_lift_iff :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} [AlgebraicStack.UniversallyInjective f]
    {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y),
    AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of k σ y) ∈
      Set.range (AlgebraicStack.Points.map f) ↔
    ∃ x : GroupoidsOver.slice (Over.mk σ) ⟶ X, Nonempty (x ≫ f ≅ y))

#check (AlgebraicGeometry.AlgebraicStack.Points.mem_range_map_of_iso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (x : GroupoidsOver.slice (Over.mk σ) ⟶ X),
    Nonempty (x ≫ f ≅ y) →
    AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of k σ y) ∈
      Set.range (AlgebraicStack.Points.map f))
