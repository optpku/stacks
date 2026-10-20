/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Product
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable (X Y : GroupoidsOver S) [AlgebraicStack X] [AlgebraicStack Y]
variable (T X' Y' : AlgebraicStacks S)

/- Lemma 94.14.1 (1): let `S` be a scheme contained in `Sch_fppf`. Let `X`, `Y` be
algebraic stacks over `S`. Then `X ×_{(Sch/S)_fppf} Y` is an algebraic stack. -/
@[stacks 04TE]
#check (AlgebraicGeometry.AlgebraicStack.prod X Y :
  AlgebraicGeometry.AlgebraicStack (CategoryTheory.FiberedCategoryOver.Groupoids.prod X Y))

/- Lemma 94.14.1 (2): the 2-fibre product `X ×_{(Sch/S)_fppf} Y` is a product in
the 2-category of algebraic stacks over `S`. -/
@[stacks 04TE]
#check (AlgebraicGeometry.AlgebraicStacks.prodHomEquiv T X' Y' :
  (T ⟶ AlgebraicGeometry.AlgebraicStacks.prod X' Y') ≌ (T ⟶ X') × (T ⟶ Y'))
