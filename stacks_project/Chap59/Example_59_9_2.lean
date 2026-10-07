module

import ReasLib.CategoryTheory.Yoneda
import StacksCheckRecall

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable (X : C)

/- Example 59.9.2: for an object `X` of `C`, the rule `U ↦ (U ⟶ X)` with
precomposition along morphisms is the representable presheaf
`CategoryTheory.yoneda.obj X : Cᵒᵖ ⥤ Type v`.
Representable presheaves need not be sheaves for every topology. -/
@[stacks 03ND] #check (CategoryTheory.Yoneda.obj_spec X :
  (∀ U : C, (CategoryTheory.yoneda.obj X).obj (Opposite.op U) = (U ⟶ X)) ∧
    (∀ {U V : C} (φ : V ⟶ U) (ψ : U ⟶ X),
      (CategoryTheory.yoneda.obj X).map φ.op ψ = φ ≫ ψ))

#check (CategoryTheory.yoneda.obj X : Cᵒᵖ ⥤ Type v)

end

end CategoryTheory
