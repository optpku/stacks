/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 016D
-/

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] (X : C)
variable {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)

/- Example 14.3.4: the constant simplicial object on `X`. -/
@[stacks 016D]
#check ((SimplicialObject.const C).obj X : SimplicialObject C)

/- Every degree of the constant simplicial object is definitionally `X`. -/
#check (rfl : ((SimplicialObject.const C).obj X).obj n = X)

/- Every structure map of the constant simplicial object is definitionally `𝟙 X`. -/
#check (rfl : ((SimplicialObject.const C).obj X).map α = 𝟙 X)

#check (SimplicialObject.const C : C ⥤ SimplicialObject C)
