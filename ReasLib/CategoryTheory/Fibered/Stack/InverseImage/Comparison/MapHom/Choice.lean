/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Coherence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Choice.Pushforward
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.HomComparison

/-!
# Choice coherence for the direct inverse-image morphism construction

This file records that changing the stackification quasi-inverse preserves the direct Hom
comparison and supplies the usual laws for its canonical choice isomorphism.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.mapHom

variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

/-- Changing the stackification quasi-inverse preserves the direct stackification comparison. -/
@[stacks 04WS "direct comparison choice coherence"]
theorem choiceIso.comparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.isoWhiskerRight (choiceIso I I' h q q')
          (StackOver.Hom.precomp I'.target I.comparisonHom) ≪≫
        comparisonIso I I' h q' =
      comparisonIso I I' h q := sorry

/-- The forward direct stackification-choice triangle commutes at every stack morphism. -/
@[stacks 04WS "direct comparison choice forward component"]
theorem choiceIso.hom.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (StackOver.Hom.precomp I'.target I.comparisonHom).map
          ((choiceIso I I' h q q').hom.app F) ≫
        (comparisonIso I I' h q').hom.app F =
      (comparisonIso I I' h q).hom.app F := sorry

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The inverse direct stackification-choice triangle commutes at every stack morphism. -/
@[stacks 04WS "direct comparison choice inverse component"]
theorem choiceIso.inv.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (comparisonIso I I' h q').inv.app F ≫
        (StackOver.Hom.precomp I'.target I.comparisonHom).map
          ((choiceIso I I' h q q').inv.app F) =
      (comparisonIso I I' h q).inv.app F := sorry

set_option maxHeartbeats 800000 in
/-- Changing the stackification quasi-inverse preserves the direct comparison after applying the
canonical Hom functor. -/
@[stacks 04WS "direct Hom-functor choice coherence"]
theorem choiceIso.homFunctorComparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.isoWhiskerRight (choiceIso I I' h q q') (homFunctor I I'.target) ≪≫
        homFunctorIso I I' h q' =
      homFunctorIso I I' h q := sorry

set_option maxHeartbeats 800000 in
/-- The forward direct-choice comparison triangle commutes at every stack morphism. -/
@[stacks 04WS "direct Hom-functor choice forward component"]
theorem choiceIso.hom.homFunctorComparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctor I I'.target).map ((choiceIso I I' h q q').hom.app F) ≫
        (homFunctorIso I I' h q').hom.app F =
      (homFunctorIso I I' h q).hom.app F := sorry

set_option maxHeartbeats 800000 in
/-- The inverse direct-choice comparison triangle commutes at every stack morphism. -/
@[stacks 04WS "direct Hom-functor choice inverse component"]
theorem choiceIso.inv.homFunctorComparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctorIso I I' h q').inv.app F ≫
        (homFunctor I I'.target).map ((choiceIso I I' h q q').inv.app F) =
      (homFunctorIso I I' h q).inv.app F := sorry

/-- The direct choice comparison from a stackification lift to itself is the identity. -/
@[simp, stacks 04WS "direct comparison choice reflexivity"]
theorem choiceIso.refl
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    choiceIso I I' h q q = Iso.refl (mapHom I I' h q) := sorry

/-- Reversing a direct choice comparison exchanges its stackification lifts. -/
@[simp, stacks 04WS "direct comparison choice symmetry"]
theorem choiceIso.symm
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    (choiceIso I I' h q q').symm = choiceIso I I' h q' q := sorry

/-- Direct choice comparisons compose transitively. -/
@[stacks 04WS "direct comparison choice transitivity"]
theorem choiceIso.trans
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' q'' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    choiceIso I I' h q q' ≪≫ choiceIso I I' h q' q'' =
      choiceIso I I' h q q'' := sorry

end StackOver.InverseImage.mapHom

end CategoryTheory
