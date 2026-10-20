/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.SourceLocus

/-!
# Unambiguous source opens

The five cases are relative dimension at most `d`, local quasi-finiteness,
unramifiedness, flatness, and étaleness. The first three assume local finite
type and commute with arbitrary base change: the empty condition on base
change means no restriction. The last two assume local finite presentation
and commute with flat, locally finite-presentation base change. In particular,
the largest flat source open then equals the pointwise flat locus.

The source omits verification of assumptions (1) and (2) of Lemma 100.9.18;
these assumptions still apply. Its references establish assumptions (3) and (4).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 100.9.20. The largest source open for bounded relative dimension. -/
@[stacks 06M5] #check (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_relativeDimensionLE :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ),
    ∃ W : OpenSubspace X, (RelativeDimensionLE (W.ι ≫ f) d ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) d →
        U.pointsSet ⊆ W.pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_relativeDimensionLE_pullback :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (d : ℕ) (W : OpenSubspace X)
    (hW : (RelativeDimensionLE (W.ι ≫ f) d ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) d →
        U.pointsSet ⊆ W.pointsSet)),
    (RelativeDimensionLE ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) d ∧
      ∀ U : OpenSubspace (pullback f g), RelativeDimensionLE (U.ι ≫ (pullback.snd f g)) d →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_relativeDimensionLE_pointsSet :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ)
    (W : OpenSubspace X) (hW : (RelativeDimensionLE (W.ι ≫ f) d ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) d →
        U.pointsSet ⊆ W.pointsSet)),
    W.pointsSet = fiberDimensionLELocus f d)

#check (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_locallyQuasiFinite :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f],
    ∃ W : OpenSubspace X, (LocallyQuasiFinite (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_locallyQuasiFinite_quasiFiniteLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f],
    (LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ (quasiFiniteLocus f).pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_locallyQuasiFinite_pullback :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X)
    (hW : (LocallyQuasiFinite (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)),
    (LocallyQuasiFinite ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) ∧
      ∀ U : OpenSubspace (pullback f g), LocallyQuasiFinite (U.ι ≫ (pullback.snd f g)) →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_locallyQuasiFinite_iff_relativeDimensionLE_zero :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X),
    (LocallyQuasiFinite (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) ↔
      (RelativeDimensionLE (W.ι ≫ f) 0 ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) 0 →
        U.pointsSet ⊆ W.pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_unramified :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f],
    ∃ W : OpenSubspace X, (Unramified (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_unramified_sourceLocus :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f],
    (Unramified ((Unramified.sourceLocus f).ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ (Unramified.sourceLocus f).pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_unramified_pullback :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X)
    (hW : (Unramified (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)),
    (Unramified ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) ∧
      ∀ U : OpenSubspace (pullback f g), Unramified (U.ι ≫ (pullback.snd f g)) →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_unramified_pointsSet :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (W : OpenSubspace X) (hW : (Unramified (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)),
    W.pointsSet = {x | UnramifiedAt f x})

#check (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_flat_of_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f],
    ∃ W : OpenSubspace X,
      (Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) ∧ W.pointsSet = {x | FlatAt f x})

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_flat_pullback :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Flat g] [LocallyOfFinitePresentation g] (W : OpenSubspace X)
    (hW : Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet),
    Flat ((W.inverseImage (pullback.fst f g)).ι ≫ pullback.snd f g) ∧
      ∀ U : OpenSubspace (pullback f g),
        Flat (U.ι ≫ pullback.snd f g) →
          U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_etale :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f],
    ∃ W : OpenSubspace X, (Etale (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Etale (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_etale_pullback :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat g] [LocallyOfFinitePresentation g]
    (W : OpenSubspace X) (hW : (Etale (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Etale (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)),
    (Etale ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) ∧
      ∀ U : OpenSubspace (pullback f g), Etale (U.ι ≫ (pullback.snd f g)) →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet))

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_etale_pointsSet :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (W : OpenSubspace X) (hW : (Etale (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Etale (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)),
    W.pointsSet = {x | EtaleAt f x})
