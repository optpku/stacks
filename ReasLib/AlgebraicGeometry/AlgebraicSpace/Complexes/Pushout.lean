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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Groupoids

/-!
# Complexes over finite-order-thickening-affine pushouts

Restriction along a finite-order-thickening-affine pushout of schemes is an
equivalence on the fibre categories of relatively perfect complexes with
vanishing negative fibre self-Ext.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- For a proper, flat morphism `f : X ⟶ B` of finite presentation, restriction
of relatively perfect complexes with vanishing negative fibre self-Ext along
a pushout in `Over S` is an equivalence of fibre categories when
`i : Z ⟶ Z'` is a finite-order thickening and `g : Z ⟶ Y` is affine. -/
instance restrictionComparison.instIsEquivalence {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    {Z Z' Y Y' : Over S} {i : Z ⟶ Z'} {g : Z ⟶ Y} {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'}
    [IsFiniteOrderThickening i.left] [IsAffineHom g.left] (h : IsPushout i g inl inr) :
    (CategoryTheory.Functor.restrictionComparison (p f) h.w).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
