module

public import ReasLib.CategoryTheory.Sites.Precoverage.Sheaf
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : Precoverage C) [J.HasPullbacks]
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.7.1: A Type-valued presheaf is a sheaf when the canonical
restriction fork of every covering family is an equalizer. On a site, the
covering-pullback capability used by this predicate follows from the site
axioms; the condition itself needs no other site axioms. -/
@[stacks 00VM]
#check (CategoryTheory.Precoverage.IsSheafOfTypes J P : Prop)

#check (CategoryTheory.Precoverage.isSheafOfTypes_iff_isSheafFor J P :
  CategoryTheory.Precoverage.IsSheafOfTypes J P ↔
    ∀ {B : C} (R : Presieve B), R ∈ J B → R.IsSheafFor P)
