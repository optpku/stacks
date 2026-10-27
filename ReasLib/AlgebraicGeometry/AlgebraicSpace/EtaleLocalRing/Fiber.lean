/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local

/-!
# Geometric fibre rings of algebraic spaces

The geometric fibre ring is the source étale local ring modulo the extension
of the maximal ideal of the target étale local ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre ring `𝒪_{X, xbar} ⧸ m_{ȳ} 𝒪_{X, xbar}` of a morphism of algebraic
spaces at a geometric point `xbar`, where `ȳ = xbar.map f`. -/
def fiberEtaleLocalRing {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) : Type u :=
  etaleLocalRing X xbar ⧸
    Ideal.map (etaleLocalRingMap f xbar)
      (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))

/-- `fiberEtaleLocalRing f xbar` is the quotient of `etaleLocalRing X xbar` by
the extension of the maximal ideal of `etaleLocalRing Y (xbar.map f)`. -/
theorem fiberEtaleLocalRing_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    fiberEtaleLocalRing f xbar =
      (etaleLocalRing X xbar ⧸
        Ideal.map (etaleLocalRingMap f xbar)
          (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))) :=
  sorry

/-- The fibre ring at a geometric point is a commutative ring, as a quotient of
the source étale local ring. -/
instance fiberEtaleLocalRing.instCommRing {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    CommRing (fiberEtaleLocalRing f xbar) :=
  inferInstanceAs
    (CommRing
      (etaleLocalRing X xbar ⧸
        Ideal.map (etaleLocalRingMap f xbar)
          (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))))

/-- The closed fibre of an étale local ring map is a local ring. -/
instance fiberEtaleLocalRing.instIsLocalRing {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    IsLocalRing (fiberEtaleLocalRing f xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
