module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Catenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Catenary decent algebraic spaces of finite type

A decent algebraic space locally of finite type over a locally Noetherian
universally catenary scheme is catenary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A decent algebraic space locally of finite type over a locally Noetherian
universally catenary scheme is catenary. -/
instance instIsCatenary_of_locallyOfFiniteType {S : Scheme.{u}}
    (X : AlgebraicSpace S) [AlgebraicGeometry.UniversallyCatenary S]
    [LocallyOfFiniteType (SchemeRealization.toBase X)] [IsDecent X] :
    IsCatenary X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
