module

public import ReasLib.CategoryTheory.RepresentablePresheaf.RelativelyRepresentable
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {F G : Cᵒᵖ ⥤ Type v} (a : F ⟶ G)
variable (ha : yoneda.relativelyRepresentable a) (hG : G.IsRepresentable)

/- Lemma 4.8.3: a relatively representable morphism with representable codomain has
representable domain. -/
@[stacks 03KC]
#check (Functor.relativelyRepresentable.domain_isRepresentable a ha hG : F.IsRepresentable)

end CategoryTheory
