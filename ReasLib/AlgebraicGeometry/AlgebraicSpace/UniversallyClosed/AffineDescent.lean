module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsAffine

/-- The target of a surjective universally closed morphism of algebraic spaces
from an affine algebraic space is affine. -/
theorem of_surjective_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [IsAffine X] : IsAffine Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsAffine
