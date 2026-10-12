/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_5_1_Comparison
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
import Mathlib.Tactic.CrossRefAttribute

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

/-- Definition 98.18.1: a category `Z` fibred in groupoids over `(Sch/S)_fppf`
satisfies condition (RS*) if for every pushout `Y' = Y ⨿_X X'` in `Over S`
whose vertices are affine, corresponding to a fibre product of `S`-algebras
`A' = A ×_B B'` with `X = Spec(B)`, `X' = Spec(B')`, `Y = Spec(A)`,
`Y' = Spec(A')`, and with `X ⟶ X'` a first-order thickening (equivalently
`B' → B` surjective of square-zero kernel), the functor of fibre categories
`restrictionComparison Z.p hw : Z.p.Fiber Y' ⥤
(Chosen.reindex Z.p toY) ⊡ (Chosen.reindex Z.p toX')` is an equivalence. -/
@[stacks 07Y8]
class HasStrongRimSchlessinger {S : Scheme.{u}} (Z : GroupoidsOver S) : Prop where
  /-- Restriction along an affine first-order-thickening pushout is an
  equivalence of fibre categories. -/
  isEquivalence_comparison :
    ∀ {X X' Y Y' : Over S}
      [IsAffine X.left] [IsAffine X'.left]
      [IsAffine Y.left] [IsAffine Y'.left]
      {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
      [IsFirstOrderThickening toX'.left]
      (h : IsPushout toX' toY fromX' fromY),
      (restrictionComparison Z.p h.w).IsEquivalence

/-- The canonical slice fibration of a scheme over `S` satisfies condition (RS*). -/
instance instHasStrongRimSchlessingerSlice {S : Scheme.{u}} (U : Over S) :
    HasStrongRimSchlessinger (GroupoidsOver.slice U) := sorry

/-- Under condition (RS*), the restriction comparison along an affine first-order
thickening pushout is an equivalence. -/
instance restrictionComparison.instIsEquivalence {S : Scheme.{u}}
    {Z : GroupoidsOver S} [HasStrongRimSchlessinger Z]
    {X X' Y Y' : Over S}
    [IsAffine X.left] [IsAffine X'.left]
    [IsAffine Y.left] [IsAffine Y'.left]
    {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    [IsFirstOrderThickening toX'.left]
    (h : IsPushout toX' toY fromX' fromY) :
    (restrictionComparison Z.p h.w).IsEquivalence :=
  HasStrongRimSchlessinger.isEquivalence_comparison h

/-- Condition (RS*) is equivalent to the restriction comparison being an
equivalence on every affine first-order-thickening pushout in `Over S`. -/
theorem hasStrongRimSchlessinger_iff {S : Scheme.{u}} (Z : GroupoidsOver S) :
    HasStrongRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S}
        [IsAffine X.left] [IsAffine X'.left]
        [IsAffine Y.left] [IsAffine Y'.left]
        {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
        [IsFirstOrderThickening toX'.left]
        (h : IsPushout toX' toY fromX' fromY),
        (restrictionComparison Z.p h.w).IsEquivalence := sorry

/-- Condition (RS*) means that every pushout in `Over S` of affine schemes, with
`X ⟶ X'` a first-order thickening, induces an equivalence of fibre categories. -/
theorem hasStrongRimSchlessinger_spec {S : Scheme.{u}} (Z : GroupoidsOver S) :
    HasStrongRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S} (toX' : X ⟶ X') (toY : X ⟶ Y)
        (fromX' : X' ⟶ Y') (fromY : Y ⟶ Y')
        (h : IsPushout toX' toY fromX' fromY),
        IsAffine X.left → IsAffine X'.left →
        IsAffine Y.left → IsAffine Y'.left →
        IsFirstOrderThickening toX'.left →
        (restrictionComparison Z.p h.w).IsEquivalence := sorry

end AlgebraicGeometry.GroupoidsOver
