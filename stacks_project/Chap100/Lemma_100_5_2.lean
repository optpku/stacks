/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective.Composition
import StacksCheckRecall

/-!
# Composition of surjective morphisms of algebraic stacks

The composition of a pair of surjective morphisms of algebraic stacks is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Surjective

/- Lemma 100.5.2: The composition of surjective morphisms is surjective. -/
@[stacks 04ZT] #check (AlgebraicGeometry.AlgebraicStack.Surjective.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g],
    Surjective (f ≫ g))

end Surjective

end AlgebraicGeometry.AlgebraicStack
