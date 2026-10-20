/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.LciFormallySmooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 97.15.3: For positive degree, the LCI Hilbert forgetful morphism of a
flat, locally finitely presented morphism representable by algebraic spaces is
formally smooth on objects. -/
@[stacks 06D9] #check (AlgebraicGeometry.FiniteHilbertStack.lciForgetToY.formallySmoothOnObjects :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [NeZero d]
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)],
    Groupoids.Hom.FormallySmoothOnObjects
      (asGroupoidsOverMor (lciForgetToY F d)))

#check (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    [FormallySmoothOnObjects p] {U U' : Over S} [IsAffine U.left]
    [IsAffine U'.left] (i : U ⟶ U') [IsFirstOrderThickening i.left]
    (y' : GroupoidsOver.slice U' ⟶ Y) (x : GroupoidsOver.slice U ⟶ X)
    (γ : x ≫ p ≅ slice.pullback i y'),
    ∃ (x' : GroupoidsOver.slice U' ⟶ X) (β : slice.pullback i x' ≅ x)
      (γ' : x' ≫ p ≅ y'), FormallySmoothOnObjects.restrictionSquare p i β γ γ')
