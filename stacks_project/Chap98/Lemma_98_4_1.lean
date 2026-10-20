/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pushout
import StacksCheckRecall

/-!
# Pushouts of thickenings and algebraic stacks

Algebraic stacks satisfy the (strong) Rim-Schlessinger condition: restriction
along a thickening-plus-affine pushout in `Over S` is an equivalence of fibre
categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits

noncomputable section

universe u

/- Lemma 98.4.1: if `S` is a scheme, `Z` is an algebraic stack over `S`, and
`Y' = Y ⨿_X X'` is a pushout in `Over S` with `X ⟶ X'` a thickening and
`X ⟶ Y` affine (see More on Morphisms, Lemma 37.14.3), then the functor of
fibre categories `restrictionComparison Z.p h.w` is an equivalence. -/
@[stacks 07WN] #check
  (AlgebraicGeometry.GroupoidsOver.restrictionComparison.instIsEquivalence_algebraicStack :
    ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {X X' Y Y' : Over S} {toX' : X ⟶ X'} {toY : X ⟶ Y}
    {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    [IsThickening toX'.left] [IsAffineHom toY.left]
    (h : IsPushout toX' toY fromX' fromY),
    (restrictionComparison Z.p h.w).IsEquivalence)
