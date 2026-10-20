/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Fubini.Limits.Comparison

/-!
# Computations for limit Fubini totalization and comparisons

This leaf records the vertex, cone-leg, morphism, and comparison-component formulas needed by
downstream calculations without requiring definitions to be unfolded.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCones

variable {M : I × J ⥤ C} (D : DiagramOfCones (curry.obj M))

/-- Curry-specialized totalization preserves the vertex of the outer cone. -/
@[simp]
lemma curryTotalFunctor.obj_pt (c : Cone D.conePoints) :
    (D.curryTotalFunctor.obj c).pt = c.pt := sorry
/- Proof strategy: unfold `curryTotalFunctor`; both totalization and `Cone.postcompose`
preserve the cone vertex. -/

/-- A curry-specialized total cone leg is the outer leg followed by the row leg. -/
@[simp, reassoc]
lemma curryTotalFunctor.obj_π_app (c : Cone D.conePoints) (p : I × J) :
    (D.curryTotalFunctor.obj c).π.app p =
      c.π.app p.1 ≫ (D.obj p.1).π.app p.2 := sorry
/- Proof strategy: unfold `curryTotalFunctor`; compute the totalization component and then
the component of `Cone.postcompose` along `currying.symm.unitIso`. -/

/-- Curry-specialized totalization is the identity on vertex morphisms. -/
@[simp]
lemma curryTotalFunctor.map_hom {c₁ c₂ : Cone D.conePoints} (α : c₁ ⟶ c₂) :
    (D.curryTotalFunctor.map α).hom = α.hom := sorry
/- Proof strategy: unfold `curryTotalFunctor` and functor composition; use
`totalConeFunctor_map_hom`, then the fact that `Cone.postcompose` retains the cone-morphism
hom field. -/

/-- The forward functor of the curry-specialized cone equivalence is the public
curry-totalization functor. -/
@[simp]
lemma curryEquivalence.functor (hD : ∀ i, IsLimit (D.obj i)) :
    (D.curryEquivalence hD).functor = D.curryTotalFunctor := sorry

section Comparisons

variable (M : I × J ⥤ C)

/-- The forward Fubini limit comparison sends a product projection to the outer projection
followed by the corresponding inner row projection. -/
@[simp, reassoc]
theorem limitIso.hom_π (D : DiagramOfCones (curry.obj M))
    (hD : ∀ i, IsLimit (D.obj i)) [HasLimit D.conePoints] [HasLimit M]
    (i : I) (j : J) :
    (limitIso (M := M) D hD).hom ≫ limit.π M (i, j) =
      limit.π D.conePoints i ≫ (D.obj i).π.app j := sorry

/-- The inverse Fubini limit comparison reconstructs a product projection from the outer and
inner row projections. -/
@[simp, reassoc]
theorem limitIso.inv_π (D : DiagramOfCones (curry.obj M))
    (hD : ∀ i, IsLimit (D.obj i)) [HasLimit D.conePoints] [HasLimit M]
    (i : I) (j : J) :
    (limitIso (M := M) D hD).inv ≫
        limit.π D.conePoints i ≫ (D.obj i).π.app j =
      limit.π M (i, j) := sorry

/-- The forward comparison between the two iterated-limit orders identifies the `E`-ordered
projection at `(j, i)` with the `D`-ordered projection at `(i, j)`. -/
@[simp, reassoc]
theorem swapIso.hom_π (D : DiagramOfCones (curry.obj M))
    (hD : ∀ i, IsLimit (D.obj i))
    (E : DiagramOfCones (curry.obj (Prod.swap J I ⋙ M)))
    (hE : ∀ j, IsLimit (E.obj j)) [HasLimit D.conePoints]
    [HasLimit E.conePoints] [HasLimit M] (i : I) (j : J) :
    (swapIso (M := M) D hD E hE).hom ≫
        limit.π E.conePoints j ≫ (E.obj j).π.app i =
      limit.π D.conePoints i ≫ (D.obj i).π.app j := sorry

/-- The inverse comparison between the two iterated-limit orders identifies the `D`-ordered
projection at `(i, j)` with the `E`-ordered projection at `(j, i)`. -/
@[simp, reassoc]
theorem swapIso.inv_π (D : DiagramOfCones (curry.obj M))
    (hD : ∀ i, IsLimit (D.obj i))
    (E : DiagramOfCones (curry.obj (Prod.swap J I ⋙ M)))
    (hE : ∀ j, IsLimit (E.obj j)) [HasLimit D.conePoints]
    [HasLimit E.conePoints] [HasLimit M] (i : I) (j : J) :
    (swapIso (M := M) D hD E hE).inv ≫
        limit.π D.conePoints i ≫ (D.obj i).π.app j =
      limit.π E.conePoints j ≫ (E.obj j).π.app i := sorry

end Comparisons

end DiagramOfCones

end CategoryTheory.Limits
