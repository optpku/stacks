/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Bicategory

universe u

/- Definition 101.13.2 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
closed if the map of topological spaces `|X| ⟶ |Y|` is closed. -/
@[stacks 0513] #check (AlgebraicGeometry.AlgebraicStack.Closed :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.13.2 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
universally closed if for every morphism of algebraic stacks `Z ⟶ Y` the map
`|Z ×_Y X| ⟶ |Z|` is closed, i.e. the base change `Z ×_Y X ⟶ Z` is closed. -/
@[stacks 0513] #check (AlgebraicGeometry.AlgebraicStack.UniversallyClosed :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
