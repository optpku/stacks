/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Naturality.Source
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Ambient.Naturality
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Direct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom comparison for the direct inverse-image morphism construction

The comparison is assembled from explicit natural isomorphisms at each intermediate layer.
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

/-- The objectwise comparison after applying the canonical Hom functor to the direct
inverse-image morphism construction. It composes the stackification counit, source naturality,
the ambient pullback-comparison isomorphism, and the ambient-to-bundled postcomposition
comparison. -/
@[stacks 04WS "inverse-image Hom comparison component"]
noncomputable def homComparisonApp
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    ((mapHom I I' h q ⋙ homFunctor I I'.target).obj F) ≅
      (postcomp S (pullbackComparison I')).obj F :=
  (FiberedCategoryOver.Pushforward.homFunctor u I.sourceChoice
      I'.target.toFiberedCategoryOver ⋙
    (StackOver.Hom.ambientEquivalence S
      (StackOver.pullback u I'.target)).functor).mapIso
        ((comparisonIso I I' h q).app F) ≪≫
  (StackOver.Hom.ambientEquivalence S
      (StackOver.pullback u I'.target)).functor.mapIso
        (FiberedCategoryOver.Pushforward.Hom.mapPostcompIso u h
          (StackOver.Hom.toMor F) I'.comparisonHom) ≪≫
  (StackOver.Hom.ambientEquivalence S
      (StackOver.pullback u I'.target)).functor.mapIso
        (((Bicategory.postcomposing S.toFiberedCategoryOver
          S'.toFiberedCategoryOver
          (StackOver.pullback u I'.target).toFiberedCategoryOver).mapIso
            (pullbackComparison.toMorIso I').symm).app
              (StackOver.Hom.toMor F)) ≪≫
  (StackOver.Hom.ambientPostcompIso (pullbackComparison I')).app F

set_option maxHeartbeats 800000 in
/-- The objectwise direct/Hom comparison is natural in stack `2`-morphisms. -/
@[stacks 04WS "inverse-image Hom comparison naturality"]
theorem homComparisonApp.naturality
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    {F G : S ⟶ S'} (eta : F ⟶ G) :
    (mapHom I I' h q ⋙ homFunctor I I'.target).map eta ≫
        (homComparisonApp I I' h q G).hom =
      (homComparisonApp I I' h q F).hom ≫
        (postcomp S (pullbackComparison I')).map eta := sorry

/-- Applying the canonical Hom functor to the direct inverse-image morphism construction
recovers postcomposition with the canonical pullback comparison. -/
@[stacks 04WS "Hom comparison for direct inverse-image morphisms"]
noncomputable def homFunctorIso
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    mapHom I I' h q ⋙ homFunctor I I'.target ≅
      postcomp S (pullbackComparison I') :=
  NatIso.ofComponents (homComparisonApp I I' h q)
    (homComparisonApp.naturality I I' h q)

set_option maxHeartbeats 800000 in
/-- The forward component of the direct inverse-image Hom comparison is its explicit four-stage
objectwise comparison. -/
@[simp, stacks 04WS "inverse-image Hom comparison forward component"]
theorem homFunctorIso.hom.app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctorIso I I' h q).hom.app F =
      (homComparisonApp I I' h q F).hom := sorry

/-- The inverse component of the direct inverse-image Hom comparison is the inverse explicit
four-stage objectwise comparison. -/
@[simp, stacks 04WS "inverse-image Hom comparison inverse component"]
theorem homFunctorIso.inv.app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctorIso I I' h q).inv.app F =
      (homComparisonApp I I' h q F).inv := sorry

/- Axiom audit: the data of `homFunctorIso` are the composite of four explicit isomorphisms;
`sorryAx` is confined to naturality, inverse laws, compatibility, and inherited proof fields. -/

end StackOver.InverseImage.mapHom

end CategoryTheory
