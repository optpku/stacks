/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.15.2: a morphism `f : X ⟶ Y` of algebraic stacks is a
universal homeomorphism if for every morphism of algebraic stacks `Z ⟶ Y` the
map of topological spaces `|Z ×_Y X| ⟶ |Z|` is a homeomorphism. -/
@[stacks 0CI7] #check (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
