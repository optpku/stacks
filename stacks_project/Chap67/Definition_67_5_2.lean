/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.5.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
surjective if the function on associated points `Points.map f : |X| → |Y|` of the
associated topological spaces is surjective. -/
@[stacks 03ME] #check (AlgebraicGeometry.AlgebraicSpace.Surjective :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.surjective_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), AlgebraicGeometry.AlgebraicSpace.Surjective f ↔
      Function.Surjective (AlgebraicGeometry.AlgebraicSpace.Points.map f))
