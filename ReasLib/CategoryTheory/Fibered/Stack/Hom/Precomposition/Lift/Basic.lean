module

public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit lifts along stack Hom precomposition

This leaf lifts postcomposition through an explicitly supplied quasi-inverse to the generic
stack-to-ambient precomposition functor. It makes no stackification assumption.

## Main declarations

* `CategoryTheory.StackOver.Hom.PrecompLift.mapFunctor` -- the
  induced functor between Hom categories from explicitly supplied quasi-inverse
  data for precomposition.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Hom.PrecompLift

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X X' : FiberedCategoryOver.{u, v, w, vS} C}
variable {Y Y' : StackOver.{u, v, w, vS} J}

/-- Lift postcomposition along an explicitly supplied quasi-inverse to precomposition. This
version owns no hidden choice and is usable without a stackification hypothesis. -/
@[stacks 04W9 "fixed-universe explicit lift along precomposition"]
noncomputable def mapFunctor
    {i : X ⟶ Y.toFiberedCategoryOver}
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    (X ⟶ X') ⥤ (Y ⟶ Y') :=
  (q.liftFunctor (X ⟶ X')).obj (Bicategory.postcomp X i')

namespace mapFunctor

/-- An explicit precomposition lift applies the chosen inverse to postcomposition with the target
map. -/
@[simp, stacks 04W9 "object formula for fixed-universe precomposition lift"]
theorem obj
    {i : X ⟶ Y.toFiberedCategoryOver}
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (mapFunctor i' q).obj F = q.inverse.obj (F ≫ i') := sorry

/-- An explicit precomposition lift applies the chosen inverse to the right-whiskered ambient
`2`-cell. -/
@[simp, stacks 04W9 "morphism formula for fixed-universe precomposition lift"]
theorem map
    {i : X ⟶ Y.toFiberedCategoryOver}
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    {F G : X ⟶ X'} (eta : F ⟶ G) :
    (mapFunctor i' q).map eta = q.inverse.map (eta ▷ i') := sorry

/-- Precomposing an explicit lift recovers postcomposition by the target map. -/
@[stacks 04W9 "comparison for fixed-universe precomposition lift"]
noncomputable def comparisonIso
    {i : X ⟶ Y.toFiberedCategoryOver}
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    mapFunctor i' q ⋙ StackOver.Hom.precomp Y' i ≅
      Bicategory.postcomp X i' :=
  Functor.QuasiInverse.liftFunctor.comparisonIso q (Bicategory.postcomp X i')

/-- Explicit precomposition lifts are independent, up to natural isomorphism,
of the supplied quasi-inverse. -/
@[stacks 04W9 "choice independence of fixed-universe precomposition lift"]
noncomputable def choiceIso
    {i : X ⟶ Y.toFiberedCategoryOver}
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    mapFunctor i' q ≅ mapFunctor i' q' :=
  Functor.QuasiInverse.liftFunctor.choiceIso q q' (Bicategory.postcomp X i')

end mapFunctor

end StackOver.Hom.PrecompLift

end CategoryTheory
