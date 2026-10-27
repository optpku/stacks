/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.FinitePointSequence

/-!
# Finite sequences of closed-point blowups of algebraic spaces

Typed checks of the finite-sequence API, re-exported for existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsPointBlowup :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsDecent X]
    (f : X' ⟶ X) (p : Points X) (hp : p ∈ closedPoints (Points X)),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isPointBlowup_iff :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsDecent X] (f : X' ⟶ X) (p : Points X)
    (hp : p ∈ closedPoints (Points X)),
    IsPointBlowup f p hp ↔
      (ClosedSubspace.ofClosedPoint p hp).pullbackDefined f ∧
        ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
          (ClosedSubspace.ofClosedPoint p hp).pullbackDefined g →
            ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence :
    {S : Scheme.{u}} → AlgebraicSpace S → AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.nil :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), PointBlowupSequence X X)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.cons :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} [IsDecent X] [IsDecent X']
      (p : Points X) (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
      (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y),
      PointBlowupSequence X Y)

namespace PointBlowupSequence

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.length :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : PointBlowupSequence X Y),
    ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.length_nil :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (nil X).length = 0)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.length_cons :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent X'] (p : Points X)
    (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
    (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y),
    (cons p hp f h_blowup tail).length = tail.length + 1)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.toSource :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : PointBlowupSequence X Y),
    Y ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.toSource_nil :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (nil X).toSource = 𝟙 X)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.toSource_cons :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent X'] (p : Points X)
    (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
    (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y),
    (cons p hp f h_blowup tail).toSource = tail.toSource ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.append :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (s : PointBlowupSequence X Y) (t : PointBlowupSequence Y Z),
    PointBlowupSequence X Z)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.length_append :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (head : PointBlowupSequence X Y) (tail : PointBlowupSequence Y Z),
    (head.append tail).length = head.length + tail.length)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.toSource_append :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (head : PointBlowupSequence X Y) (tail : PointBlowupSequence Y Z),
    (head.append tail).toSource = tail.toSource ≫ head.toSource)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.EveryCenterOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : PointBlowupSequence X Y) (T : Set (Points X)),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.everyCenterOver_nil :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)),
    (nil X).EveryCenterOver T ↔ True)

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.everyCenterOver_cons :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent X'] (p : Points X)
    (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
    (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y)
    (T : Set (Points X)),
    (cons p hp f h_blowup tail).EveryCenterOver T ↔
      p ∈ T ∧ tail.EveryCenterOver (Points.map f ⁻¹' T))

#check (AlgebraicGeometry.AlgebraicSpace.PointBlowupSequence.everyCenterOver_append :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (head : PointBlowupSequence X Y) (tail : PointBlowupSequence Y Z)
    (T : Set (Points X)),
    (head.append tail).EveryCenterOver T ↔
      head.EveryCenterOver T ∧
        tail.EveryCenterOver (Points.map head.toSource ⁻¹' T))

end PointBlowupSequence

end AlgebraicGeometry.AlgebraicSpace
