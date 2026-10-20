module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

universe u v

/-- The diagonal of a presheaf satisfies the lifted morphism property if every
pairwise pullback of Yoneda sections is representable and its comparison to the
product of the representables satisfies that lifted property. -/
theorem presheaf_diag {C : Type u} [Category.{v} C]
    [hasBinaryProducts : HasBinaryProducts C] {P : MorphismProperty C}
    {F : Cᵒᵖ ⥤ Type v}
    (h_rep : ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      (pullback ξ ξ').IsRepresentable)
    (hP : ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      P.presheaf (prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ'))) :
    P.presheaf (diag F) := sorry

/-- The diagonal of a presheaf satisfies the lifted morphism property exactly
when every pairwise pullback of Yoneda sections is representable and its comparison
to the product of the representables satisfies that lifted property. -/
theorem presheaf_diag_iff {C : Type u} [Category.{v} C]
    [hasBinaryProducts : HasBinaryProducts C] {P : MorphismProperty C}
    {F : Cᵒᵖ ⥤ Type v} :
    P.presheaf (diag F) ↔
      ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
        (pullback ξ ξ').IsRepresentable ∧
          P.presheaf (prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ')) := sorry

end CategoryTheory.MorphismProperty
