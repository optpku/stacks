module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 016J
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (U U' : CosimplicialObject C)

/- Definition 14.5.1: a cosimplicial object of `C` is the canonical functor-category object
`SimplexCategory ⥤ C`. -/
@[stacks 016J]
#check (CosimplicialObject C)

#check (U ⟶ U')
#check (CosimplicialObject (Type u))
#check (CosimplicialObject AddCommGrpCat)
