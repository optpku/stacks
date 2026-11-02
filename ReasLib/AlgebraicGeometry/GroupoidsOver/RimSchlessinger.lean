/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Artinian.Local
public import ReasLib.CategoryTheory.Fibered.RestrictionComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# The Rim-Schlessinger condition for categories fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` satisfies condition (RS) when
restriction along every Artinian finite-type closed-immersion pushout in `Over S`
induces an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- A category `Z` fibred in groupoids over `(Sch/S)_fppf` satisfies condition
(RS) if for every pushout
`Y' = Y ⨿_X X'` in `Over S` whose vertices are spectra of local Artinian rings, of
finite type over `S`, and with `X ⟶ X'` a closed immersion, the functor of fibre
categories `restrictionComparison Z.p hw : Z.p.Fiber Y' ⥤
(Chosen.reindex Z.p toY) ⊡ (Chosen.reindex Z.p toX')` is an equivalence. -/
class HasRimSchlessinger {S : Scheme.{u}}
    (Z : GroupoidsOver S) : Prop where
  /-- Restriction along an Artinian finite-type closed-immersion pushout is an
  equivalence of fibre categories. -/
  isEquivalence_comparison :
    ∀ {X X' Y Y' : Over S}
      [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
      [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
      [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
      [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
      {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
      [IsClosedImmersion toX'.left]
      (h : IsPushout toX' toY fromX' fromY),
      (restrictionComparison Z.p h.w).IsEquivalence

/-- The canonical slice fibration of a scheme over a base scheme satisfies
condition (RS). -/
instance instHasRimSchlessingerSlice {S : Scheme.{u}}
    (U : Over S) : HasRimSchlessinger (GroupoidsOver.slice U) := sorry

/-- Under condition (RS), the restriction comparison along an Artinian finite-type
closed-immersion pushout is an equivalence. -/
instance restrictionComparison.instIsEquivalence_of_hasRimSchlessinger {S : Scheme.{u}}
    {Z : GroupoidsOver S} [HasRimSchlessinger Z]
    {X X' Y Y' : Over S}
    [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
    [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
    [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
    [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
    {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    [IsClosedImmersion toX'.left]
    (h : IsPushout toX' toY fromX' fromY) :
    (restrictionComparison Z.p h.w).IsEquivalence :=
  HasRimSchlessinger.isEquivalence_comparison h

/-- Condition (RS) is equivalent to the restriction comparison being an equivalence
on every Artinian finite-type closed-immersion pushout in `Over S`. -/
theorem hasRimSchlessinger_iff {S : Scheme.{u}}
    (Z : GroupoidsOver S) :
    HasRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S}
        [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
        [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
        [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
        [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
        {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
        [IsClosedImmersion toX'.left]
        (h : IsPushout toX' toY fromX' fromY),
        (restrictionComparison Z.p h.w).IsEquivalence := sorry

/-- Condition (RS) means that every pushout in `Over S` of spectra of local Artinian
rings of finite type over `S`, with `X ⟶ X'` a closed immersion, induces an
equivalence of fibre categories. -/
theorem hasRimSchlessinger_spec {S : Scheme.{u}}
    (Z : GroupoidsOver S) :
    HasRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S} (toX' : X ⟶ X') (toY : X ⟶ Y)
        (fromX' : X' ⟶ Y') (fromY : Y ⟶ Y')
        (h : IsPushout toX' toY fromX' fromY),
        IsSpecLocalArtinian X.left → IsSpecLocalArtinian X'.left →
        IsSpecLocalArtinian Y.left → IsSpecLocalArtinian Y'.left →
        Scheme.Hom.FiniteType X.hom → Scheme.Hom.FiniteType X'.hom →
        Scheme.Hom.FiniteType Y.hom → Scheme.Hom.FiniteType Y'.hom →
        IsClosedImmersion toX'.left →
        (restrictionComparison Z.p h.w).IsEquivalence := sorry

end AlgebraicGeometry.GroupoidsOver
