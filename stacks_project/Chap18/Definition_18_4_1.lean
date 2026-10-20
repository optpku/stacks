module

public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ Type v) (X U : C)

/- Definition 18.4.1 (03A7): the free abelian presheaf is objectwise free abelianization. -/
@[stacks 03A7 "presheaf"]
#check (FreeAbelianPresheaf.obj G : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/- Definition 18.4.1 (03A7), representable specialization. -/
@[stacks 03A7 "representable"]
#check (FreeAbelianYoneda.obj X : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/- The objectwise evaluation formula is exposed by the neutral owner. -/
#check (FreeAbelianPresheaf.obj_obj G (op U) :
  (FreeAbelianPresheaf.obj G).obj (op U) =
    AddCommGrpCat.of (FreeAbelianGroup (G.obj (op U))))

end CategoryTheory
