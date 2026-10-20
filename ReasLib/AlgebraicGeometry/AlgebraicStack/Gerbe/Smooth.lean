/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- A gerbe morphism of algebraic stacks is smooth. -/
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Smooth f := sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
