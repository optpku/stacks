module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints

/-!
# Finite irreducible components of integral algebraic spaces

An integral algebraic space has finitely many irreducible components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral algebraic space has finitely many irreducible components. -/
instance instHasFiniteIrreducibleComponents_of_isIntegral {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsIntegral X] : HasFiniteIrreducibleComponents X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
