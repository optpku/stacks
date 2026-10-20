/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Pushout
import StacksCheckRecall

/-!
# Lemma 99.13.7

Restriction of `pFpFlatProperGroupoids` along a thickening-plus-affine
pushout in `Over B` is an equivalence of fibre categories.
-/

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.Spaces

universe u

/- Lemma 99.13.7: restriction along a thickening-affine pushout is an
equivalence on the finite-presentation, flat, proper fibre categories. -/
@[stacks 0D1J]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.restrictionComparison.instIsEquivalence :
  ∀ {B : Scheme.{u}}
    {T T' S S' : Over B} {i : T ⟶ T'} {f : T ⟶ S} {inl : T' ⟶ S'} {inr : S ⟶ S'}
    [IsThickening i.left] [IsAffineHom f.left] (h : IsPushout i f inl inr),
    (restrictionComparison (pFpFlatProperGroupoids B) h.w).IsEquivalence)
