/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Fibered.RestrictionComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids

/-!
# Coherent sheaves over thickening-affine pushouts

Restriction along a thickening-affine pushout of schemes is an equivalence
on the fibre categories of finitely presented flat modules with proper support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- For a finite-presentation morphism `f : X ⟶ B` of algebraic spaces,
restriction of finitely presented quasi-coherent modules, flat over the test
scheme with proper support, along a pushout of schemes in `Over S` is an
equivalence of fibre categories when `i : Z ⟶ Z'` is a thickening and
`g : Z ⟶ Y` is affine. -/
instance restrictionComparison.instIsEquivalence {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    {Z Z' Y Y' : Over S} {i : Z ⟶ Z'} {g : Z ⟶ Y} {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'}
    [IsThickening i.left] [IsAffineHom g.left] (h : IsPushout i g inl inr) :
    (restrictionComparison (p f) h.w).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
