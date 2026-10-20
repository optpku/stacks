module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import StacksCheckRecall

/-!
@stack 016A
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (U U' : SimplicialObject C)

/- Definition 14.3.1: a simplicial object of `C` is the canonical functor-category object
`SimplexCategoryᵒᵖ ⥤ C`. -/
@[stacks 016A]
#check (SimplicialObject C)

#check (U ⟶ U')
#check SSet.{u}
#check (SimplicialObject AddCommGrpCat)
