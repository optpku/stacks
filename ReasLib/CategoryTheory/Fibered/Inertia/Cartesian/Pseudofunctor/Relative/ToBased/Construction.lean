module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.MapArrow.Construction
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory

/-!
# Forgetting fibred pseudo-comma squares

The forgetful pseudofunctor from fibred categories to based categories acts
on pseudo-comma arrows through the neutral `Pseudofunctor.mapArrow`
construction.  This leaf owns only that specialization; all generic square
and coherence data remain in the bicategorical comma library.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- Forget a fibred pseudo-comma square to the corresponding pseudo-comma
square of based categories.

This is the arrow action of the canonical forgetful pseudofunctor, so its
endpoint, square, `2`-cell, and comparison data are inherited from
`Pseudofunctor.mapArrow`. -/
noncomputable def toBased :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
      (Bicategory.PseudoComma
        (Pseudofunctor.id (BasedCategory.{vS, w} C))
        (Pseudofunctor.id (BasedCategory.{vS, w} C))) :=
  ((FiberedCategoryOver.toBased C).toPseudofunctor).mapArrow

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
