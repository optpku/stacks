/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.AlmostBlowup.Tests
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.MappedSquare
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Square

/-!
# Groupoid-valued descent tests on a chosen big h-site

This module records comparison-functor formulations of descent for affine
flat-proper covers and two canonical families of almost-blowup squares.
-/

@[expose] public section

open CategoryTheory Limits Limits.CategoricalPullback

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigHSite.GroupoidDescent

/-- Groupoid-valued descent for affine-target surjective flat proper
morphisms of finite presentation, tested using every explicit self-pullback. -/
def IsAffineFlatProperSurjective (Schh : ChosenBigHSite.{u, v})
    (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S)) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U)
      [IsAffine ((ChosenBigSite.sliceToScheme Schh S).obj U)]
      [Surjective ((ChosenBigSite.sliceToScheme Schh S).map f)]
      [Flat ((ChosenBigSite.sliceToScheme Schh S).map f)]
      [IsProper ((ChosenBigSite.sliceToScheme Schh S).map f)]
      [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme Schh S).map f)]
      (h : ChosenPullback f f),
    (Pseudofunctor.mapCommSqOver (Functor.fiberPseudofunctor 𝒮.p)
      (h.square.flip.op)).comparison.IsEquivalence

/-- Groupoid-valued descent for represented nilpotent principal-center
almost-blow-up squares, invariant under isomorphism of represented squares. -/
def IsPrincipalCenter (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S)) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : A) (J : Ideal A) (hJfg : J.FG)
      (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) (sq : Square (Over S)),
    (sq.map (ChosenBigSite.sliceToScheme Schh S) ≅
      (Spec.quotientMap_isAlmostBlowupSquare A f J hJfg hJ).square) →
        (Pseudofunctor.mapCommSqOver (Functor.fiberPseudofunctor 𝒮.p)
          (sq.flip.op)).comparison.IsEquivalence

/-- Groupoid-valued descent for represented two-generator projective
almost-blow-up squares, invariant under isomorphism of represented squares. -/
def IsTwoGenerator (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S)) : Prop :=
  ∀ (A : CommRingCat.{u}) (f₁ f₂ : A) (sq : Square (Over S)),
    (sq.map (ChosenBigSite.sliceToScheme Schh S) ≅
      (TwoGeneratorProj.toSpec_isAlmostBlowupSquare A f₁ f₂).square) →
        (Pseudofunctor.mapCommSqOver (Functor.fiberPseudofunctor 𝒮.p)
          (sq.flip.op)).comparison.IsEquivalence

/-- Restriction of a stack in groupoids for the h topology to the Zariski
topology is again a stack in groupoids. -/
theorem zariskiOfIsStack (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S))
    (h𝒮 : IsStack.InGroupoids (bigTopology Schh S) 𝒮.p) :
    IsStack.InGroupoids (bigZariskiTopology Schh S) 𝒮.p := sorry

/-- An h-stack in groupoids has descent along every affine-target surjective
flat proper morphism of finite presentation. -/
theorem affineFlatProperDescentOfIsStack
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S))
    (h𝒮 : IsStack.InGroupoids (bigTopology Schh S) 𝒮.p) :
    IsAffineFlatProperSurjective Schh S 𝒮 := sorry

/-- An h-stack in groupoids has descent for represented nilpotent
principal-center almost-blow-up squares. -/
theorem principalCenterDescentOfIsStack
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S))
    (h𝒮 : IsStack.InGroupoids (bigTopology Schh S) 𝒮.p) :
    IsPrincipalCenter Schh S 𝒮 := sorry

/-- An h-stack in groupoids has descent for represented two-generator
projective almost-blow-up squares. -/
theorem twoGeneratorDescentOfIsStack
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S))
    (h𝒮 : IsStack.InGroupoids (bigTopology Schh S) 𝒮.p) :
    IsTwoGenerator Schh S 𝒮 := sorry

/-- Zariski descent, affine flat-proper-surjective descent, and descent for
the two canonical almost-blow-up test families imply the h-stack condition. -/
theorem ofZariskiFlatProperExampleDescent
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S))
    (h_zariski : IsStack.InGroupoids (bigZariskiTopology Schh S) 𝒮.p)
    (h_flatProper : IsAffineFlatProperSurjective Schh S 𝒮)
    (h_principal : IsPrincipalCenter Schh S 𝒮)
    (h_twoGenerator : IsTwoGenerator Schh S 𝒮) :
    IsStack.InGroupoids (bigTopology Schh S) 𝒮.p := sorry

/-- A category fibred in groupoids on a chosen big h-site slice is an h-stack
exactly when it satisfies Zariski descent, affine flat-proper-surjective
descent, and descent for the two canonical almost-blow-up test families. -/
theorem iffZariskiAndFlatProperExampleDescent
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S)) :
    IsStack.InGroupoids (bigTopology Schh S) 𝒮.p ↔
      IsStack.InGroupoids (bigZariskiTopology Schh S) 𝒮.p ∧
        IsAffineFlatProperSurjective Schh S 𝒮 ∧
          IsPrincipalCenter Schh S 𝒮 ∧ IsTwoGenerator Schh S 𝒮 := sorry

end AlgebraicGeometry.ChosenBigHSite.GroupoidDescent
