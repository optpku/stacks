/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Pushout
import StacksCheckRecall

/-!
# Lemma 99.16.9

Restriction of `Complexes` along a finite-order-thickening-plus-affine pushout
in `Over S` is an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.16.9: in Situation 99.16.3, restriction along a pushout in `Over S`
with `i : Z ⟶ Z'` a finite-order thickening and `g : Z ⟶ Y` affine is an
equivalence from the fibre over `Y'` to the categorical fibre product of the
fibres over `Y` and `Z'` over the fibre over `Z`. -/
@[stacks 0DLK] #check
  (AlgebraicGeometry.AlgebraicSpace.Complexes.restrictionComparison.instIsEquivalence :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {Z Z' Y Y' : Over S} {i : Z ⟶ Z'} {g : Z ⟶ Y} {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'}
    [IsFiniteOrderThickening i.left] [IsAffineHom g.left] (h : IsPushout i g inl inr),
    (CategoryTheory.Functor.restrictionComparison
      (AlgebraicGeometry.AlgebraicSpace.Complexes.p f) h.w).IsEquivalence)
