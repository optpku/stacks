module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer

/-!
# Separation properties of closed subspaces

Closed subspaces inherit quasi-separatedness and decency from their ambient spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- A closed subspace of a quasi-separated algebraic space is quasi-separated. -/
def instIsQuasiSeparated {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiSeparated X] (Y : ClosedSubspace X) : IsQuasiSeparated Y.X :=
  sorry

/-- A closed subspace of a decent algebraic space is decent. -/
def instIsDecent {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Y : ClosedSubspace X) : IsDecent Y.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
