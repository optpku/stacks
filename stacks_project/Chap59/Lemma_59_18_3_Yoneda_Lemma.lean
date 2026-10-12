/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {U : C} {F : Cᵒᵖ ⥤ Type v}

/- Lemma 59.18.3 (Yoneda Lemma) -/
@[stacks 03ON] #check (CategoryTheory.RepresentablePresheaf.homEquiv :
  (yoneda.obj U ⟶ F) ≃ F.obj (Opposite.op U))

#check (CategoryTheory.yonedaEquiv_naturality :
  ∀ {V : C} (α : yoneda.obj U ⟶ F) (morphism : V ⟶ U),
    F.map morphism.op (CategoryTheory.RepresentablePresheaf.homEquiv α) =
      CategoryTheory.RepresentablePresheaf.homEquiv (yoneda.map morphism ≫ α))

#check (CategoryTheory.yonedaEquiv_comp :
  ∀ {G : Cᵒᵖ ⥤ Type v} (α : yoneda.obj U ⟶ F) (β : F ⟶ G),
    CategoryTheory.RepresentablePresheaf.homEquiv (α ≫ β) =
      β.app (Opposite.op U) (CategoryTheory.RepresentablePresheaf.homEquiv α))

end CategoryTheory
