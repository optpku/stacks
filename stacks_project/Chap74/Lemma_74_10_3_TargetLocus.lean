/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.TargetLocus

/-! # Target locus construction and membership interfaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.isFppfToEtalePrecoverage :
    ∀ {S : Scheme.{u}} (K : Precoverage (AlgebraicSpace S)),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.targetLocusPoints :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Set (Points Y))

#check (AlgebraicGeometry.AlgebraicSpace.mem_targetLocusPoints :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {y : Points Y},
    y ∈ targetLocusPoints P f ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι))

#check (AlgebraicGeometry.AlgebraicSpace.isOpen_targetLocusPoints :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    IsOpen (targetLocusPoints P f))

#check (AlgebraicGeometry.AlgebraicSpace.targetLocus :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    OpenSubspace Y)

#check (AlgebraicGeometry.AlgebraicSpace.targetLocus_pointsSet :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    (targetLocus P f).pointsSet = targetLocusPoints P f)

#check (AlgebraicGeometry.AlgebraicSpace.mem_targetLocus :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {y : Points Y},
    y ∈ (targetLocus P f).pointsSet ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι))

#check (AlgebraicGeometry.AlgebraicSpace.targetLocus_maximal :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (V : OpenSubspace Y) (hV : P (pullback.snd f V.ι)),
    ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι)

#check (AlgebraicGeometry.AlgebraicSpace.targetLocus_spec :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (targetLocus P f).pointsSet = targetLocusPoints P f ∧
      ∀ V : OpenSubspace Y, V.pointsSet = targetLocusPoints P f →
        ∃! χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι)
