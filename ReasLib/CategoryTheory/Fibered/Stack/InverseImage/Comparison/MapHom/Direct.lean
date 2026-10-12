/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage
public import ReasLib.CategoryTheory.Fibered.Stack.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct inverse-image action on stack morphisms

This file constructs the functor on stack-morphism categories directly from
an explicit pushforward inversion family and an explicit stackification lift.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable {u : C ⥤ D}

/-- The functor on stack-morphism categories induced directly by the two stackification
comparisons. It first pushes forward the underlying source morphism using the supplied inversion
family and then applies an explicitly supplied universal morphism lift for `I.comparisonHom`. This
construction owns no hidden choice and does not use continuity of `u`. -/
@[stacks 04WS "inverse-image action on stack morphisms"]
noncomputable def mapHom
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    (S ⟶ S') ⥤ (I.target ⟶ I'.target) :=
  StackOver.Pushforward.mapFunctor u h_pushforward ⋙
    StackOver.Hom.PrecompLift.mapFunctor I'.comparisonHom q

namespace mapHom

/-- The direct inverse-image functor first pushes a stack morphism forward and then applies the
chosen inverse to postcomposition with the target stackification comparison. -/
@[simp, stacks 04WS "inverse-image action object computation"]
theorem obj
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (mapHom I I' h_pushforward q).obj F =
      q.inverse.obj
        ((StackOver.Pushforward.mapFunctor u h_pushforward).obj F ≫ I'.comparisonHom) := sorry

/-- The direct inverse-image functor sends a stack `2`-cell by pushforward, right whiskering with
the target comparison, and the chosen inverse functor. -/
@[simp, stacks 04WS "inverse-image action map computation"]
theorem map
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    {F G : S ⟶ S'} (eta : F ⟶ G) :
    (mapHom I I' h_pushforward q).map eta =
      q.inverse.map
        ((StackOver.Pushforward.mapFunctor u h_pushforward).map eta ▷ I'.comparisonHom) := sorry

/-- Precomposing the explicit stackification lift recovers pushforward followed
by the target stackification comparison. -/
@[stacks 04WS "inverse-image action comparison isomorphism"]
noncomputable def comparisonIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    mapHom I I' h_pushforward q ⋙
        StackOver.Hom.precomp I'.target I.comparisonHom ≅
      StackOver.Pushforward.mapFunctor u h_pushforward ⋙
        Bicategory.postcomp
          (FiberedCategoryOver.pushforward u S.toFiberedCategoryOver h_pushforward.source)
          I'.comparisonHom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (StackOver.Pushforward.mapFunctor u h_pushforward)
      (StackOver.Hom.PrecompLift.mapFunctor.comparisonIso
        (i := I.comparisonHom) I'.comparisonHom q)

/-- Two explicit choices of the stackification lift give naturally isomorphic
inverse-image morphism functors. -/
@[stacks 04WS "inverse-image action choice isomorphism"]
noncomputable def choiceIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    mapHom I I' h_pushforward q ≅ mapHom I I' h_pushforward q' :=
  Functor.isoWhiskerLeft
    (StackOver.Pushforward.mapFunctor u h_pushforward)
    (StackOver.Hom.PrecompLift.mapFunctor.choiceIso
      (i := I.comparisonHom) I'.comparisonHom q q')

/-- Lemma 8.12.12 (2) (tag 04WS): under the hypotheses of Sites, Lemma 7.21.8, every explicitly
chosen stackification lift inducing inverse image is an equivalence between the morphism
categories of stacks. -/
@[stacks 04WS]
instance isEquivalence
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.IsEquivalence (mapHom I I' h_pushforward q) := sorry

end mapHom

-- Data audit: both noncanonical inputs are explicit. The object and morphism actions reduce to
-- those of the two constituent functors, whose direct computation APIs are imported above.

end StackOver.InverseImage

end CategoryTheory
