/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Choice.Pushforward
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Presentation

/-!
# Pushforward-choice naturality of inverse-image presentations

Changing the proof supplying pushforward inversion preserves both the direct Hom comparison and
the canonical isomorphism from the direct construction to the Hom-quasi-inverse construction.
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

/-- Changing the pushforward inversion proof preserves the direct comparison after applying the
canonical Hom functor. -/
@[stacks 04WS "presentation inversion-choice Hom coherence"]
theorem inversionChoiceIso.homFunctorComparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.isoWhiskerRight (inversionChoiceIso I I' h h' q)
          (homFunctor I I'.target) ≪≫
        homFunctorIso I I' h' q =
      homFunctorIso I I' h q := sorry

set_option maxHeartbeats 800000 in
/-- The forward pushforward-choice/Hom-comparison triangle commutes on every stack morphism. -/
@[stacks 04WS "presentation inversion-choice forward component"]
theorem inversionChoiceIso.hom.homFunctorComparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctor I I'.target).map
          ((inversionChoiceIso I I' h h' q).hom.app F) ≫
        (homFunctorIso I I' h' q).hom.app F =
      (homFunctorIso I I' h q).hom.app F := sorry

/-- The inverse pushforward-choice/Hom-comparison triangle commutes on every stack morphism. -/
@[stacks 04WS "presentation inversion-choice inverse component"]
theorem inversionChoiceIso.inv.homFunctorComparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctorIso I I' h' q).inv.app F ≫
        (homFunctor I I'.target).map
          ((inversionChoiceIso I I' h h' q).inv.app F) =
      (homFunctorIso I I' h q).inv.app F := sorry

/-- Presentation independence is natural in the proof supplying pushforward inversion. -/
@[stacks 04WS "presentation inversion-choice coherence"]
theorem homQuasiInverseIso.inversionChoice
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target)) :
    inversionChoiceIso I I' h h' q_stack ≪≫
        homQuasiInverseIso I I' h' q_stack q_hom =
      homQuasiInverseIso I I' h q_stack q_hom := sorry

/-- The forward pushforward-choice square for presentation independence commutes objectwise. -/
@[stacks 04WS "presentation inversion-choice forward component"]
theorem homQuasiInverseIso.hom.inversionChoice_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (inversionChoiceIso I I' h h' q_stack).hom.app F ≫
        (homQuasiInverseIso I I' h' q_stack q_hom).hom.app F =
      (homQuasiInverseIso I I' h q_stack q_hom).hom.app F := sorry

/-- The inverse pushforward-choice square for presentation independence commutes objectwise. -/
@[stacks 04WS "presentation inversion-choice inverse component"]
theorem homQuasiInverseIso.inv.inversionChoice_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (homQuasiInverseIso I I' h' q_stack q_hom).inv.app F ≫
        (inversionChoiceIso I I' h h' q_stack).inv.app F =
      (homQuasiInverseIso I I' h q_stack q_hom).inv.app F := sorry

end StackOver.InverseImage.mapHom

end CategoryTheory
