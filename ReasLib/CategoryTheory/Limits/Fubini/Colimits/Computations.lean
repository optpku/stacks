module

public import ReasLib.CategoryTheory.Limits.Fubini.Colimits.Comparison

/-!
# Computations for colimit Fubini totalization and comparisons

This leaf records the vertex, cocone-leg, morphism, and comparison-component formulas needed by
downstream calculations without requiring definitions to be unfolded.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCocones

variable {M : I × J ⥤ C} (D : DiagramOfCocones (curry.obj M))

/-- Curry-specialized totalization preserves the vertex of the outer cocone. -/
@[simp]
lemma curryTotalFunctor.obj_pt (c : Cocone D.coconePoints) :
    (D.curryTotalFunctor.obj c).pt = c.pt := sorry
/- Proof strategy: unfold `curryTotalFunctor`; both totalization and
`Cocone.precompose` preserve the cocone vertex. -/

/-- A curry-specialized total cocone leg is the row leg followed by the outer leg. -/
@[simp, reassoc]
lemma curryTotalFunctor.obj_ι_app (c : Cocone D.coconePoints) (p : I × J) :
    (D.curryTotalFunctor.obj c).ι.app p =
      (D.obj p.1).ι.app p.2 ≫ c.ι.app p.1 := sorry
/- Proof strategy: unfold `curryTotalFunctor`; compute the totalization component and then
the component of `Cocone.precompose` along `currying.symm.unitIso`. -/

/-- Curry-specialized totalization is the identity on vertex morphisms. -/
@[simp]
lemma curryTotalFunctor.map_hom {c₁ c₂ : Cocone D.coconePoints} (α : c₁ ⟶ c₂) :
    (D.curryTotalFunctor.map α).hom = α.hom := sorry
/- Proof strategy: unfold `curryTotalFunctor` and functor composition; use
`totalCoconeFunctor_map_hom`, then the fact that `Cocone.precompose` retains the
cocone-morphism hom field. -/

/-- The forward functor of the curry-specialized cocone equivalence is the public
curry-totalization functor. -/
@[simp]
lemma curryEquivalence.functor (hD : ∀ i, IsColimit (D.obj i)) :
    (D.curryEquivalence hD).functor = D.curryTotalFunctor := sorry

section Comparisons

variable (M : I × J ⥤ C)

/-- The forward Fubini colimit comparison sends an inner row coprojection followed by an outer
coprojection to the coprojection of the product-indexed diagram. -/
@[simp, reassoc]
theorem colimitIso.hom_ι (D : DiagramOfCocones (curry.obj M))
    (hD : ∀ i, IsColimit (D.obj i)) [HasColimit D.coconePoints] [HasColimit M]
    (i : I) (j : J) :
    (D.obj i).ι.app j ≫ colimit.ι D.coconePoints i ≫
        (colimitIso (M := M) D hD).hom =
      colimit.ι M (i, j) := sorry

/-- The inverse Fubini colimit comparison expands a product coprojection into its inner row
coprojection followed by its outer coprojection. -/
@[simp, reassoc]
theorem colimitIso.inv_ι (D : DiagramOfCocones (curry.obj M))
    (hD : ∀ i, IsColimit (D.obj i)) [HasColimit D.coconePoints] [HasColimit M]
    (i : I) (j : J) :
    colimit.ι M (i, j) ≫ (colimitIso (M := M) D hD).inv =
      (D.obj i).ι.app j ≫ colimit.ι D.coconePoints i := sorry

/-- The forward comparison between the two iterated-colimit orders carries the `D`-ordered
coprojection at `(i, j)` to the `E`-ordered coprojection at `(j, i)`. -/
@[simp, reassoc]
theorem swapIso.hom_ι (D : DiagramOfCocones (curry.obj M))
    (hD : ∀ i, IsColimit (D.obj i))
    (E : DiagramOfCocones (curry.obj (Prod.swap J I ⋙ M)))
    (hE : ∀ j, IsColimit (E.obj j)) [HasColimit D.coconePoints]
    [HasColimit E.coconePoints] [HasColimit M] (i : I) (j : J) :
    (D.obj i).ι.app j ≫ colimit.ι D.coconePoints i ≫
        (swapIso (M := M) D hD E hE).hom =
      (E.obj j).ι.app i ≫ colimit.ι E.coconePoints j := sorry

/-- The inverse comparison between the two iterated-colimit orders carries the `E`-ordered
coprojection at `(j, i)` back to the `D`-ordered coprojection at `(i, j)`. -/
@[simp, reassoc]
theorem swapIso.inv_ι (D : DiagramOfCocones (curry.obj M))
    (hD : ∀ i, IsColimit (D.obj i))
    (E : DiagramOfCocones (curry.obj (Prod.swap J I ⋙ M)))
    (hE : ∀ j, IsColimit (E.obj j)) [HasColimit D.coconePoints]
    [HasColimit E.coconePoints] [HasColimit M] (i : I) (j : J) :
    (E.obj j).ι.app i ≫ colimit.ι E.coconePoints j ≫
        (swapIso (M := M) D hD E hE).inv =
      (D.obj i).ι.app j ≫ colimit.ι D.coconePoints i := sorry

end Comparisons

end DiagramOfCocones

end CategoryTheory.Limits
