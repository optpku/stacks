/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.RestrictionComparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushouts of thickenings and algebraic stacks

Restriction of an algebraic stack along a thickening-plus-affine pushout of
schemes over a base scheme is an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For an algebraic stack over a scheme, restriction along a pushout in the
category of schemes over that base, with one leg a thickening and the other
affine, is an equivalence from the fibre over the pushout to the categorical
pullback of the other two fibres over the common fibre. -/
@[stacks 07WN]
instance restrictionComparison.instIsEquivalence_algebraicStack
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {X X' Y Y' : Over S} {toX' : X ⟶ X'} {toY : X ⟶ Y}
    {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    [IsThickening toX'.left] [IsAffineHom toY.left]
    (h : IsPushout toX' toY fromX' fromY) :
    (restrictionComparison Z.p h.w).IsEquivalence := sorry

end AlgebraicGeometry.GroupoidsOver
