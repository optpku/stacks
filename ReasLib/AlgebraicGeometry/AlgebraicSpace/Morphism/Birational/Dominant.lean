module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Dominant

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components is dominant. -/
instance of_isBirational {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] : Dominant f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Dominant
