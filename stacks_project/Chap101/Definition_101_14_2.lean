/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.14.2: a morphism `f : X ⟶ Y` of algebraic stacks is
universally injective if for every morphism of algebraic stacks `Z ⟶ Y` the
map `|Z ×_Y X| ⟶ |Z|` is injective. -/
@[stacks 0CI2] #check (AlgebraicGeometry.AlgebraicStack.UniversallyInjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)
