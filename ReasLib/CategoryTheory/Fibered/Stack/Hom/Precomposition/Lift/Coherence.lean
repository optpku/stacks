/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Components

/-!
# Coherence of precomposition lift choices

The canonical comparison between two explicit precomposition lifts intertwines their counit
comparisons and satisfies the expected identity, symmetry, and transitivity laws.
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

/-- Changing the quasi-inverse used for a precomposition lift preserves its comparison after
precomposition. -/
@[stacks 04W9 "comparison coherence for fixed-universe precomposition choice"]
theorem choiceIso.comparison
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    Functor.isoWhiskerRight (choiceIso i' q q')
          (StackOver.Hom.precomp Y' i) ≪≫
        comparisonIso i' q' =
      comparisonIso i' q := sorry

/-- The forward precomposition-lift choice triangle commutes at every ambient morphism. -/
@[stacks 04W9 "forward comparison coherence component for fixed-universe precomposition choice"]
theorem choiceIso.hom.comparison_app
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (StackOver.Hom.precomp Y' i).map ((choiceIso i' q q').hom.app F) ≫
        (comparisonIso i' q').hom.app F =
      (comparisonIso i' q).hom.app F := sorry

/-- The inverse precomposition-lift choice triangle commutes at every ambient morphism. -/
@[stacks 04W9 "inverse comparison coherence component for fixed-universe precomposition choice"]
theorem choiceIso.inv.comparison_app
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (comparisonIso i' q').inv.app F ≫
        (StackOver.Hom.precomp Y' i).map ((choiceIso i' q q').inv.app F) =
      (comparisonIso i' q).inv.app F := sorry

/-- The precomposition-lift choice comparison from a quasi-inverse to itself is the identity. -/
@[simp, stacks 04W9 "identity law for fixed-universe precomposition choice"]
theorem choiceIso.refl
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    choiceIso i' q q = Iso.refl (mapFunctor i' q) := sorry

/-- Reversing a precomposition-lift choice comparison exchanges its quasi-inverses. -/
@[simp, stacks 04W9 "symmetry law for fixed-universe precomposition choice"]
theorem choiceIso.symm
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    (choiceIso i' q q').symm = choiceIso i' q' q := sorry

/-- Precomposition-lift choice comparisons compose transitively. -/
@[stacks 04W9 "transitivity law for fixed-universe precomposition choice"]
theorem choiceIso.trans
    (i' : X' ⟶ Y'.toFiberedCategoryOver)
    (q q' q'' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    choiceIso i' q q' ≪≫ choiceIso i' q' q'' = choiceIso i' q q'' := sorry

end StackOver.Hom.PrecompLift.mapFunctor

end CategoryTheory
