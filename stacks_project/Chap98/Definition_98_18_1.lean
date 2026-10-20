/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap98.Definition_98_5_1_Comparison
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger
import StacksCheckRecall

/-!
# The strong Rim-Schlessinger condition for categories fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` satisfies condition (RS*)
when restriction along every affine first-order-thickening pushout in `Over S`
induces an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Definition 98.18.1: the strong Rim-Schlessinger condition for a category
fibred in groupoids over `(Sch/S)_fppf`. -/
@[stacks 07Y8] #check (AlgebraicGeometry.GroupoidsOver.HasStrongRimSchlessinger :
  ∀ {S : Scheme.{u}} (Z : GroupoidsOver S), Prop)

#check (AlgebraicGeometry.GroupoidsOver.instHasStrongRimSchlessingerSlice :
  ∀ {S : Scheme.{u}} (U : Over S),
    HasStrongRimSchlessinger (GroupoidsOver.slice U))

#check (AlgebraicGeometry.GroupoidsOver.restrictionComparison.instIsEquivalence :
  ∀ {S : Scheme.{u}}
    {Z : GroupoidsOver S} [HasStrongRimSchlessinger Z]
    {X X' Y Y' : Over S}
    [IsAffine X.left] [IsAffine X'.left]
    [IsAffine Y.left] [IsAffine Y'.left]
    {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    [IsFirstOrderThickening toX'.left]
    (h : IsPushout toX' toY fromX' fromY),
    (restrictionComparison Z.p h.w).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.hasStrongRimSchlessinger_iff :
  ∀ {S : Scheme.{u}} (Z : GroupoidsOver S),
    HasStrongRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S}
        [IsAffine X.left] [IsAffine X'.left]
        [IsAffine Y.left] [IsAffine Y'.left]
        {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
        [IsFirstOrderThickening toX'.left]
        (h : IsPushout toX' toY fromX' fromY),
        (restrictionComparison Z.p h.w).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.hasStrongRimSchlessinger_spec :
  ∀ {S : Scheme.{u}} (Z : GroupoidsOver S),
    HasStrongRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S} (toX' : X ⟶ X') (toY : X ⟶ Y)
        (fromX' : X' ⟶ Y') (fromY : Y ⟶ Y')
        (h : IsPushout toX' toY fromX' fromY),
        IsAffine X.left → IsAffine X'.left →
        IsAffine Y.left → IsAffine Y'.left →
        IsFirstOrderThickening toX'.left →
        (restrictionComparison Z.p h.w).IsEquivalence)

end AlgebraicGeometry.GroupoidsOver
