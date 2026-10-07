module

public import ReasLib.CategoryTheory.Adjunction.Representability
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (u : C ⥤ D)
variable (h : ∀ Y : D, (u.op ⋙ yoneda.obj Y).IsRepresentable)

/- Lemma 4.24.2: pointwise representability of `X ↦ (u.obj X ⟶ Y)` implies that `u` is a left
adjoint. -/
@[stacks 0A8B]
#check (isLeftAdjoint_of_objwise_hom_isRepresentable u h : u.IsLeftAdjoint)

end CategoryTheory.Functor
