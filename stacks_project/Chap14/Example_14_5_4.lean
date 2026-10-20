module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 016M
-/

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] (X : C)
variable {n m : SimplexCategory} (α : n ⟶ m)

/- Example 14.5.4: the constant cosimplicial object on `X`. -/
@[stacks 016M]
#check ((CosimplicialObject.const C).obj X : CosimplicialObject C)

/- Every degree of the constant cosimplicial object is definitionally `X`. -/
#check (rfl : ((CosimplicialObject.const C).obj X).obj n = X)

/- Every structure map of the constant cosimplicial object is definitionally `𝟙 X`. -/
#check (rfl : ((CosimplicialObject.const C).obj X).map α = 𝟙 X)

#check (CosimplicialObject.const C : C ⥤ CosimplicialObject C)
