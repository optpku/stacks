/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

section

variable {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
variable [AlgebraicStack X]
variable [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]

/- Situation 107.2.1: `X` is an algebraic stack locally of finite type over
a locally Noetherian scheme `S`. -/
@[stacks 0DQU] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType :
    ∀ {T : Scheme.{u}} {Y Z : GroupoidsOver T} [AlgebraicStack Y] [AlgebraicStack Z],
      (Y ⟶ Z) → Prop)

#check (IsLocallyNoetherian S : Prop)
#check (AlgebraicStack X : Prop)
#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
  (baseProjection.{u + 1, u, u + 1} X) : Prop)

end
