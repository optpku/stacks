/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import stacks_project.Chap98.Definition_98_5_1_SpecLocalArtinian
public import stacks_project.Chap98.Definition_98_5_1_Comparison
public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

/-!
# The Rim-Schlessinger condition for categories fibred in groupoids

Restriction along local Artinian finite-type closed-immersion pushouts induces
an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.GroupoidsOver
open scoped CategoricalPullback

universe u

/- Definition 98.5.1: the Rim-Schlessinger condition for a category fibred in
groupoids over a locally Noetherian scheme. -/
@[stacks 07WP] #check (AlgebraicGeometry.GroupoidsOver.HasRimSchlessinger :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (Z : GroupoidsOver S),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.instHasRimSchlessingerSlice :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (U : Over S),
    HasRimSchlessinger (GroupoidsOver.slice U))

#check (AlgebraicGeometry.GroupoidsOver.restrictionComparison.instIsEquivalence_of_hasRimSchlessinger :
  ∀ {S : Scheme.{u}}
    [IsLocallyNoetherian S] {Z : GroupoidsOver S} [HasRimSchlessinger Z]
    {X X' Y Y' : Over S}
    [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
    [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
    [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
    [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
    {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    [IsClosedImmersion toX'.left]
    (h : IsPushout toX' toY fromX' fromY),
    (restrictionComparison Z.p h.w).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.hasRimSchlessinger_iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (Z : GroupoidsOver S),
    HasRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S}
        [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
        [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
        [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
        [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
        {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
        [IsClosedImmersion toX'.left]
        (h : IsPushout toX' toY fromX' fromY),
        (restrictionComparison Z.p h.w).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.hasRimSchlessinger_spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (Z : GroupoidsOver S),
    HasRimSchlessinger Z ↔
      ∀ {X X' Y Y' : Over S} (toX' : X ⟶ X') (toY : X ⟶ Y)
        (fromX' : X' ⟶ Y') (fromY : Y ⟶ Y')
        (h : IsPushout toX' toY fromX' fromY),
        IsSpecLocalArtinian X.left → IsSpecLocalArtinian X'.left →
        IsSpecLocalArtinian Y.left → IsSpecLocalArtinian Y'.left →
        Scheme.Hom.FiniteType X.hom → Scheme.Hom.FiniteType X'.hom →
        Scheme.Hom.FiniteType Y.hom → Scheme.Hom.FiniteType Y'.hom →
        IsClosedImmersion toX'.left →
        (restrictionComparison Z.p h.w).IsEquivalence)

#check (AlgebraicGeometry.Scheme.Pushout.fromY_isClosedImmersion_of_isSpecLocalArtinian :
  ∀ {S : Scheme.{u}}
    {X X' Y Y' : Over S}
    [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
    [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
    {toX' : X ⟶ X'} {toY : X ⟶ Y}
    {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (h : IsPushout toX' toY fromX' fromY)
    [IsClosedImmersion toX'.left],
    IsClosedImmersion fromY.left)
