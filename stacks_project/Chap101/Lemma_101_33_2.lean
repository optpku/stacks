/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth.Composition
import StacksCheckRecall

/-!
# Composition of smooth morphisms of algebraic stacks

The composition of a pair of smooth morphisms of algebraic stacks is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Smooth

/- Lemma 101.33.2: The composition of smooth morphisms is smooth. -/
@[stacks 075V] #check (AlgebraicGeometry.AlgebraicStack.Smooth.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicStack.Smooth f]
    [AlgebraicGeometry.AlgebraicStack.Smooth g],
    AlgebraicGeometry.AlgebraicStack.Smooth (f ≫ g))

end Smooth

end AlgebraicGeometry.AlgebraicStack
