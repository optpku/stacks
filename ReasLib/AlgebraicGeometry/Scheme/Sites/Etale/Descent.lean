/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- For a surjective integral morphism of schemes `f : X ⟶ Y`, canonical descent
along the singleton family `{f}` is an equivalence between Type-valued small
étale sheaves on `Y` and descent data on `X`. -/
theorem descentIsEquivalenceOfSurjectiveIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

/-- Canonical singleton descent for a surjective integral morphism of schemes
is an equivalence of categories of Type-valued small étale sheaves. -/
instance singletonDescent_isEquivalence_of_surjectiveIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfSurjectiveIntegral f

/-- For a surjective proper morphism of schemes `f : X ⟶ Y`, canonical descent
along the singleton family `{f}` is an equivalence between Type-valued small
étale sheaves on `Y` and descent data on `X`. -/
theorem descentIsEquivalenceOfSurjectiveProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [IsProper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

/-- Canonical singleton descent for a surjective proper morphism of schemes
is an equivalence of categories of Type-valued small étale sheaves. -/
instance singletonDescent_isEquivalence_of_surjectiveProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsProper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfSurjectiveProper f

/-- Canonical singleton descent for Type-valued small étale sheaves along a
morphism `f : X ⟶ Y` is an equivalence if it is an equivalence after base change
to a surjective integral morphism `g : Z ⟶ Y` and to its self-overlap
`Z ×_Y Z`. -/
theorem descentIsEquivalenceOfBaseChangeOfSurjectiveIntegral
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [IsIntegralHom g]
    (hZ : (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ pullback.snd f g)).IsEquivalence)
    (hZZ : (pseudofunctor.toDescentData
        (fun _ : PUnit.{1} ↦ pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

/-- Canonical singleton descent for Type-valued small étale sheaves along a
morphism `f : X ⟶ Y` is an equivalence if it is an equivalence after base change
to a surjective proper morphism `g : Z ⟶ Y` and to its self-overlap
`Z ×_Y Z`. -/
theorem descentIsEquivalenceOfBaseChangeOfSurjectiveProper
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [IsProper g]
    (hZ : (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ pullback.snd f g)).IsEquivalence)
    (hZZ : (pseudofunctor.toDescentData
        (fun _ : PUnit.{1} ↦ pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

/-- For a surjective, flat, locally finitely presented morphism of schemes
`f : X ⟶ Y`, canonical descent along the singleton family `{f}` is an equivalence
between Type-valued small étale sheaves on `Y` and descent data on `X`. -/
theorem descentIsEquivalenceOfSurjectiveFlatLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

/-- Canonical singleton descent for a surjective, flat, locally finitely presented
morphism of schemes is an equivalence of categories of Type-valued small étale sheaves. -/
instance singletonDescent_isEquivalence_of_fppf
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfSurjectiveFlatLocallyOfFinitePresentation f

/-- For an fppf covering family of schemes, the canonical functor from
Type-valued small étale sheaves on the target to descent data along the family
is an equivalence of categories. -/
theorem descentIsEquivalenceOfFppfCovering
    {ι : Type v} {X : Scheme.{u}} {X_i : ι → Scheme.{u}}
    (f : ∀ i, X_i i ⟶ X) (h : FppfCovering (fun i ↦ Over.mk (f i))) :
    (pseudofunctor.toDescentData f).IsEquivalence := sorry

/-- Canonical descent along an fppf covering family is an equivalence of
categories of Type-valued small étale sheaves. -/
instance descent_isEquivalence_of_fppfCovering
    {ι : Type v} {X : Scheme.{u}} {X_i : ι → Scheme.{u}}
    (f : ∀ i, X_i i ⟶ X) [Fact (FppfCovering (fun i ↦ Over.mk (f i)))] :
    (pseudofunctor.toDescentData f).IsEquivalence :=
  descentIsEquivalenceOfFppfCovering f
    (Fact.out : FppfCovering (fun i ↦ Over.mk (f i)))

end AlgebraicGeometry.Scheme.EtaleSheaf
