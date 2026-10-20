/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat

/-!
# Composition of flat morphisms of algebraic stacks

The composition of a pair of flat morphisms of algebraic stacks is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Flat

/-- The composition of flat morphisms of algebraic stacks is flat. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    Flat (f ≫ g) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
