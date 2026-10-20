module

public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : C) (F G : Cᵒᵖ ⥤ Type v)
variable (A : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/- Lemma 18.4.2 (03A8) (1): the Yoneda Hom/sections equivalence. -/
@[stacks 03A8 "Yoneda"]
#check (yonedaEquiv : (yoneda.obj U ⟶ F) ≃ F.obj (op U))

/- Lemma 18.4.2 (03A8) (2): the objectwise free-forgetful adjunction for presheaves. -/
@[stacks 03A8 "free-forgetful adjunction"]
#check (FreeAbelianPresheaf.homEquiv G A :
  (FreeAbelianPresheaf.obj G ⟶ A) ≃
    (G ⟶ A ⋙ forget AddCommGrpCat.{v}))

/- Lemma 18.4.2 (03A8) (3): maps from a free abelian representable are sections. -/
@[stacks 03A8 "free abelian representable"]
#check (FreeAbelianYoneda.homEquiv U A :
  (FreeAbelianYoneda.obj U ⟶ A) ≃ A.obj (op U))

end CategoryTheory
