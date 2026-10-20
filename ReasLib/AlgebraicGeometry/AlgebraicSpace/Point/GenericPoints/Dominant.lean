module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Irreducible

/-! # Generic points under dominant morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A dominant morphism of irreducible decent algebraic spaces sends a generic
point of the source to a generic point of the target. -/
theorem map_mem_genericPoints_of_isDominant {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] [IsIrreducible X]
    [IsIrreducible Y] (f : X ⟶ Y) [Dominant f] {x : Points X}
    (hx : x ∈ genericPoints X) : Points.map f x ∈ genericPoints Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
