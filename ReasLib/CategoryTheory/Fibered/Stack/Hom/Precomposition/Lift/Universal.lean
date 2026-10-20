module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Basic

/-!
# Universal property of explicit precomposition lifts

This leaf specializes the universal comparison for a quasi-inverse lift to stack Hom
categories. Downstream users can state uniqueness entirely in terms of `mapFunctor`,
`StackOver.Hom.precomp`, and bicategorical postcomposition.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Hom.PrecompLift.mapFunctor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X X' : FiberedCategoryOver.{u, v, w, vS} C}
variable {Y Y' : StackOver.{u, v, w, vS} J}
variable {i : X ⟶ Y.toFiberedCategoryOver}

/-- A candidate precomposition lift equipped with the expected comparison is canonically
isomorphic to the explicit lift formed from `q`. -/
@[stacks 04W9 "uniqueness of fixed-universe precomposition lift"]
noncomputable def isoOfComparison
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (L : (X ⟶ X') ⥤ (Y ⟶ Y'))
    (alpha : L ⋙ StackOver.Hom.precomp Y' i ≅
      Bicategory.postcomp X i') :
    L ≅ mapFunctor i' q :=
  Functor.QuasiInverse.liftFunctor.isoOfComparison q L
    (Bicategory.postcomp X i') alpha

/-- The canonical isomorphism from a candidate precomposition lift recovers its supplied
comparison after precomposition. -/
@[stacks 04W9 "comparison recovery for fixed-universe precomposition lift uniqueness"]
theorem isoOfComparison.comparison
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (L : (X ⟶ X') ⥤ (Y ⟶ Y'))
    (alpha : L ⋙ StackOver.Hom.precomp Y' i ≅
      Bicategory.postcomp X i') :
    Functor.isoWhiskerRight (isoOfComparison i' q L alpha)
          (StackOver.Hom.precomp Y' i) ≪≫
        comparisonIso i' q =
      alpha := sorry

/-- Compatibility with the supplied comparison uniquely characterizes the canonical
precomposition-lift isomorphism. -/
@[stacks 04W9 "uniqueness criterion for fixed-universe precomposition lift"]
theorem isoOfComparison.eq_iff
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (L : (X ⟶ X') ⥤ (Y ⟶ Y'))
    (alpha : L ⋙ StackOver.Hom.precomp Y' i ≅
      Bicategory.postcomp X i')
    (beta : L ≅ mapFunctor i' q) :
    beta = isoOfComparison i' q L alpha ↔
      Functor.isoWhiskerRight beta (StackOver.Hom.precomp Y' i) ≪≫
          comparisonIso i' q =
        alpha := sorry

/-- Applying precomposition-lift uniqueness to the canonical comparison gives the identity
isomorphism. -/
@[simp, stacks 04W9 "identity case of fixed-universe precomposition lift uniqueness"]
theorem isoOfComparison.self
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    isoOfComparison i' q (mapFunctor i' q) (comparisonIso i' q) =
      Iso.refl (mapFunctor i' q) := sorry

/- Axiom audit: the canonical isomorphism is the generic data-clean comparison for an explicit
quasi-inverse lift; `sorryAx` is confined to its theorem-valued universal-property API. -/

end StackOver.Hom.PrecompLift.mapFunctor

end CategoryTheory
