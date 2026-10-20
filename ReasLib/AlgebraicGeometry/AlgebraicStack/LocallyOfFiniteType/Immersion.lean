/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-!
# Immersions of algebraic stacks are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (Immersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- An immersion of algebraic stacks is locally of finite type. -/
@[stacks 06FV]
instance of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Immersion f] :
    LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
