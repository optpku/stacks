/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedSequence

/-!
# Finite sequences of normalized blowups of algebraic spaces

A finite composable sequence of normalized blowups at closed points of decent
algebraic spaces. Each bundled step is an ordinary closed-point blowup followed
by the canonical absolute normalization of its source, as in Definition 89.5.1.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence :
  {S : Scheme.{u}} → AlgebraicSpace S → AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.nil :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), NormalizedBlowupSequence X X)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.cons :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y),
    NormalizedBlowupSequence X Y)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.length :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, NormalizedBlowupSequence X Y → ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.length_nil :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (NormalizedBlowupSequence.nil X).length = 0)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.length_cons :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y),
    (NormalizedBlowupSequence.cons step tail).length = tail.length + 1)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.toSource :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, NormalizedBlowupSequence X Y → (Y ⟶ X))

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.toSource_nil :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (NormalizedBlowupSequence.nil X).toSource = 𝟙 X)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.toSource_cons :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y),
    (NormalizedBlowupSequence.cons step tail).toSource = tail.toSource ≫ step.hom)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.EveryCenterOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    NormalizedBlowupSequence X Y → Set (Points X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.everyCenterOver_nil :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)),
    (NormalizedBlowupSequence.nil X).EveryCenterOver T ↔ True)

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence.everyCenterOver_cons :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y)
    (T : Set (Points X)),
    (NormalizedBlowupSequence.cons step tail).EveryCenterOver T ↔
      step.point ∈ T ∧ tail.EveryCenterOver (Points.map step.hom ⁻¹' T))
