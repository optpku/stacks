/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.ValuativeCriterion
import StacksCheckRecall

/-!
# Quasi-separated morphisms with uniqueness are separated

A quasi-separated morphism of algebraic stacks that satisfies uniqueness in the
valuative criterion is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Separated

/- Lemma 101.41.2: If `f : X ⟶ Y` is a quasi-separated morphism of algebraic
stacks and `f` satisfies the uniqueness part of the valuative criterion, then
`f` is separated. -/
@[stacks 0CLT] #check
  (AlgebraicGeometry.AlgebraicStack.Separated.of_valuativeCriterion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [QuasiSeparated f] [ValuativeCriterion.Uniqueness f], Separated f)

end AlgebraicGeometry.AlgebraicStack.Separated
