/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation.FiniteType
import StacksCheckRecall

/-!
# Finite presentation morphisms of algebraic stacks are of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.27.4: A morphism of algebraic stacks which is locally of finite
presentation is locally of finite type. A morphism of finite presentation is
of finite type. -/
@[stacks 06Q5] #check
  (AlgebraicGeometry.AlgebraicStack.locallyOfFiniteType_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y), [LocallyOfFinitePresentation f] → LocallyOfFiniteType f)

#check (AlgebraicGeometry.AlgebraicStack.finiteType_of_finitePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), [FinitePresentation f] → FiniteType f)

end AlgebraicGeometry.AlgebraicStack
