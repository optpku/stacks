module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cleavage
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of fibered categories along a functor

For a functor `u : C ⥤ D` and a fibered category `X` over `D`, the pullback `u ᵖ X` is the
fibered category over `C` whose total category is the categorical pullback of `X.p` along `u`.
This leaf owns only the object construction and its projection computation.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace FiberedCategoryOver

/-- Definition 8.12.4 (tag 04WE): the pullback fibered category `u ᵖ X` along a functor
`u : C ⥤ D`. Its total category is the categorical pullback of `X.p` along `u`, and its
projection is the first projection `π₁ u X.p`. -/
@[stacks 04WE]
abbrev pullback (u : C ⥤ D) (X : FiberedCategoryOver.{uD, vD, uS, vS} D) :
    FiberedCategoryOver.{uC, vC, max uC (max uS vD), max vC vS} C :=
  ofFunctor (CategoricalPullback.π₁ u X.p)

/-- Notation: `u ᵖ X` for the pullback fibered category. -/
scoped infixr:100 " ᵖ " => pullback

/-- The total category of a pulled-back fibred category is the defining categorical pullback. -/
@[simp, stacks 04WE "pullback total-category readout"]
theorem pullback_total (u : C ⥤ D) (X : FiberedCategoryOver.{uD, vD, uS, vS} D) :
    (pullback u X).total = CategoricalPullback u X.p := sorry

/-- Definition 8.12.4 (tag 04WE): the projection of the pullback fibred category is the
canonical categorical-pullback projection. -/
@[stacks 04WE, simp]
theorem pullback_p (u : C ⥤ D) (X : FiberedCategoryOver.{uD, vD, uS, vS} D) :
    (pullback u X).p = CategoricalPullback.π₁ u X.p := sorry

end FiberedCategoryOver

end CategoryTheory
