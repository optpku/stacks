/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Locality of étale local rings

The étale local ring of an algebraic space at a geometric point is a local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale local ring of an algebraic space at a geometric point is a local ring. -/
instance etaleLocalRing.instIsLocalRingAtGeometricPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) : IsLocalRing (etaleLocalRing X xbar) :=
  sorry

/-- The étale local ring map of a morphism of algebraic spaces is a local
homomorphism. -/
instance etaleLocalRingMap.instIsLocalHom {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    IsLocalHom (etaleLocalRingMap f xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
