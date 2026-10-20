module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map.EtaleSquare

/-!
# Flatness at a point via étale local rings
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A morphism of algebraic spaces is flat at a point if and only if its
canonical map of étale local rings at a geometric point over that point is flat. -/
theorem flatAt_iff_etaleLocalRingMap_flat (f : X ⟶ Y) (xbar : GeometricPoint X)
    (x : Points X) (hx : xbar.liesOver x) :
    FlatAt f x ↔ (etaleLocalRingMap f xbar).Flat :=
  sorry

/-- Flatness at the image of a geometric point is equivalent to flatness of the
induced étale local-ring map. -/
theorem flatAt_iff_etaleLocalRingMap_flat_image (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    FlatAt f xbar.image ↔ (etaleLocalRingMap f xbar).Flat :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
