module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Basic

/-!
# Relative dimension of finite locally free morphisms of algebraic spaces

A finite locally free morphism of algebraic spaces has relative dimension `0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree

/-- A finite locally free morphism of algebraic spaces has relative dimension
`0`. -/
instance instRelativeDimension_zero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteLocallyFree f] : RelativeDimension f 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree
