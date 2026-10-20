module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiFinite

/-- A finite morphism of algebraic spaces is quasi-finite. -/
instance of_isFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsFinite f] : QuasiFinite f :=
  sorry

end QuasiFinite

end AlgebraicGeometry.AlgebraicSpace
