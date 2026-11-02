/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Basic

/-!
# Target naturality of precomposition lifts

An explicit quasi-inverse to precomposition lifts the whole target-variable
postcomposition functor. Thus target `2`-cells act before any pointwise specialization, and the
comparison and choice isomorphisms are natural in the target comparison.
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

/-- Precomposition lifting, functorial in the target comparison `X' ⟶ Y'`. Its object at `i'`
is `mapFunctor i' q`, while its morphism action lifts left whiskering by target `2`-cells. -/
@[stacks 04W9 "target-natural fixed-universe precomposition lift"]
noncomputable def targetFunctor
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    (X' ⟶ Y'.toFiberedCategoryOver) ⥤
      ((X ⟶ X') ⥤ (Y ⟶ Y')) :=
  Functor.QuasiInverse.liftFunctor.diagram q
    (Bicategory.postcomposing X X' Y'.toFiberedCategoryOver)

namespace targetFunctor

/-- Evaluating target-functorial precomposition lifting at a target comparison recovers the
pointwise Hom-category lift. -/
@[simp, stacks 04W9 "object formula for target-natural precomposition lift"]
theorem obj
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (i' : X' ⟶ Y'.toFiberedCategoryOver) :
    (targetFunctor X' q).obj i' = mapFunctor i' q := rfl

/-- A target `2`-cell acts on a lifted ambient morphism by left whiskering and then applying the
chosen quasi-inverse. -/
@[simp, stacks 04W9 "morphism formula for target-natural precomposition lift"]
theorem map_app
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    {i' j' : X' ⟶ Y'.toFiberedCategoryOver} (eta : i' ⟶ j')
    (F : X ⟶ X') :
    ((targetFunctor X' q).map eta).app F = q.inverse.map (F ◁ eta) := rfl

/-- The precomposition-lift comparison assembled before specializing the target comparison. This is
the target-natural form of `mapFunctor.comparisonIso`. -/
@[stacks 04W9 "target-natural comparison for fixed-universe precomposition lift"]
noncomputable def comparisonNatIso
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    targetFunctor X' q ⋙
        (Functor.whiskeringRight (X ⟶ X') (Y ⟶ Y')
          (X ⟶ Y'.toFiberedCategoryOver)).obj
          (StackOver.Hom.precomp Y' i) ≅
      Bicategory.postcomposing X X' Y'.toFiberedCategoryOver :=
  Functor.QuasiInverse.liftFunctor.diagram.comparisonIso q
    (Bicategory.postcomposing X X' Y'.toFiberedCategoryOver)

/-- The component of the target-natural comparison at `i'` is the pointwise precomposition-lift
comparison. -/
@[simp, stacks 04W9 "component of target-natural precomposition comparison"]
theorem comparisonNatIso.app
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (i' : X' ⟶ Y'.toFiberedCategoryOver) :
    (comparisonNatIso X' q).app i' = mapFunctor.comparisonIso i' q := by
  apply Iso.ext
  change 𝟙 _ ≫ ((mapFunctor.comparisonIso i' q).hom ≫ 𝟙 _) =
    (mapFunctor.comparisonIso i' q).hom
  simp only [Category.id_comp, Category.comp_id]

/-- Changing the explicit quasi-inverse gives an isomorphism of the complete target-variable
precomposition lift functors. -/
@[stacks 04W9 "target-natural choice independence of fixed-universe precomposition lift"]
noncomputable def choiceIso
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    targetFunctor X' q ≅ targetFunctor X' q' :=
  Functor.QuasiInverse.liftFunctor.diagram.choiceIso q q'
    (Bicategory.postcomposing X X' Y'.toFiberedCategoryOver)

/-- The target-variable choice isomorphism specializes to the pointwise choice isomorphism. -/
@[simp, stacks 04W9 "component of target-natural precomposition choice"]
theorem choiceIso.app
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (i' : X' ⟶ Y'.toFiberedCategoryOver) :
    (choiceIso X' q q').app i' = mapFunctor.choiceIso i' q q' := rfl

/-- Target-variable choice independence preserves the target-natural precomposition comparison. -/
@[stacks 04W9 "comparison coherence for target-natural precomposition choice"]
theorem choiceIso.comparison
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    Functor.isoWhiskerRight (choiceIso X' q q')
          ((Functor.whiskeringRight (X ⟶ X') (Y ⟶ Y')
            (X ⟶ Y'.toFiberedCategoryOver)).obj
            (StackOver.Hom.precomp Y' i)) ≪≫
        comparisonNatIso X' q' =
      comparisonNatIso X' q := by
  apply Iso.ext
  apply NatTrans.ext
  funext i'
  change (Functor.isoWhiskerRight ((choiceIso X' q q').app i')
      (StackOver.Hom.precomp Y' i) ≪≫ (comparisonNatIso X' q').app i').hom =
    ((comparisonNatIso X' q).app i').hom
  rw [choiceIso.app, comparisonNatIso.app, comparisonNatIso.app]
  exact congrArg Iso.hom (Functor.QuasiInverse.liftFunctor.choiceIso.comparison q q'
    (Bicategory.postcomp X i'))

/-- The target-variable choice comparison from a quasi-inverse to itself is the identity. -/
@[simp, stacks 04W9 "identity law for target-natural precomposition choice"]
theorem choiceIso.refl
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    choiceIso X' q q = Iso.refl (targetFunctor X' q) := by
  apply Iso.ext
  apply NatTrans.ext
  funext i'
  exact congrArg Iso.hom (Functor.QuasiInverse.liftFunctor.choiceIso.refl q
    (Bicategory.postcomp X i'))

/-- Reversing a target-variable choice comparison exchanges its quasi-inverses. -/
@[simp, stacks 04W9 "symmetry law for target-natural precomposition choice"]
theorem choiceIso.symm
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    (choiceIso X' q q').symm = choiceIso X' q' q := by
  apply Iso.ext
  apply NatTrans.ext
  funext i'
  exact congrArg Iso.hom (Functor.QuasiInverse.liftFunctor.choiceIso.symm q q'
    (Bicategory.postcomp X i'))

/-- Target-variable choice comparisons compose transitively. -/
@[stacks 04W9 "transitivity law for target-natural precomposition choice"]
theorem choiceIso.trans
    (X' : FiberedCategoryOver.{u, v, w, vS} C)
    {i : X ⟶ Y.toFiberedCategoryOver}
    (q q' q'' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i)) :
    choiceIso X' q q' ≪≫ choiceIso X' q' q'' = choiceIso X' q q'' := by
  apply Iso.ext
  apply NatTrans.ext
  funext i'
  exact congrArg Iso.hom (Functor.QuasiInverse.liftFunctor.choiceIso.trans q q' q''
    (Bicategory.postcomp X i'))

/- Axiom audit: the functor and both natural isomorphisms are composites and whiskerings of
explicit functorial data; the computation and coherence proofs reduce to these constructions
and the proved choice laws for quasi-inverse lifts. -/

end targetFunctor

end StackOver.Hom.PrecompLift

end CategoryTheory
