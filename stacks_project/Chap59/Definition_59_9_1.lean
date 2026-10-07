module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import ReasLib.Algebra.Category.Grp.Presheaf.Basic
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Definition 59.9.1 (1): a presheaf of sets on a category C is a functor
   Cᵒᵖ ⥤ Type w. -/
@[stacks 03NC] #check
  (CategoryTheory.Presheaf.{u, v, w} C : Type (max v w u (w + 1)))

/- Definition 59.9.1 (2): an abelian presheaf on a category C is a functor
   Cᵒᵖ ⥤ AddCommGrpCat.{w}. -/
@[stacks 03NC] #check
  (AddCommGrpCat.Presheaf.{u, v, w} C : Type (max v w u (w + 1)))

end CategoryTheory
