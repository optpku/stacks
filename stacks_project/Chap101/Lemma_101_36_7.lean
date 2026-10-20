/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified.QuasiFinite

/-!
# Unramified morphisms of algebraic stacks are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.36.7: An unramified morphism of algebraic stacks is locally
quasi-finite. -/
@[stacks 0H2Z] #check (AlgebraicGeometry.AlgebraicStack.locallyQuasiFinite_of_unramified :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f], LocallyQuasiFinite f)

end AlgebraicGeometry.AlgebraicStack
