/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.Smooth
import StacksCheckRecall

/-!
# Smooth morphisms of algebraic stacks are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.33.5: A smooth morphism of algebraic stacks is locally of finite
presentation. -/
@[stacks 0DNP] #check
  (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_of_smooth :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [Smooth f], LocallyOfFinitePresentation f)

end AlgebraicGeometry.AlgebraicStack
