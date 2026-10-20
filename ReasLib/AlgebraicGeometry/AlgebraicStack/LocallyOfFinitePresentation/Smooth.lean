/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Smooth morphisms of algebraic stacks are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A smooth morphism of algebraic stacks is locally of finite presentation. -/
instance locallyOfFinitePresentation_of_smooth {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Smooth f] : LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.AlgebraicStack
