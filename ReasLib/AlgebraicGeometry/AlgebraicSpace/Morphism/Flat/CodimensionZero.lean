module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Codimension-zero points under flat morphisms of algebraic spaces

A flat morphism of algebraic spaces sends points of codimension `0` to points of
codimension `0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Under a flat morphism of algebraic spaces, a point whose local ring has
dimension zero maps to a point whose local ring has dimension zero. -/
theorem localRingDimAt_map_eq_zero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] {x : Points X} (hx : localRingDimAt x = 0) :
    localRingDimAt (Points.map f x) = 0 :=
  sorry

/-- The map on points induced by a flat morphism of algebraic spaces sends
codimension-`0` points of the source into codimension-`0` points of the target. -/
theorem mapsTo_localRingDimAt_eq_zero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] :
    Set.MapsTo (Points.map f) (setOf fun x : Points X ↦ localRingDimAt x = 0)
      (setOf fun y : Points Y ↦ localRingDimAt y = 0) := by
  intro x hx
  exact localRingDimAt_map_eq_zero f hx

end AlgebraicGeometry.AlgebraicSpace.Flat
