/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (Immersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An immersion of algebraic stacks is unramified. -/
instance unramified_of_immersion {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Immersion f] :
    Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
