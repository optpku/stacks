module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.FiniteType

/-!
# Locally of finite type over Nagata algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a Nagata target has
Nagata source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- The source of a locally-of-finite-type morphism of algebraic spaces with Nagata target
is Nagata. -/
theorem isNagata {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNagata Y] :
    IsNagata X :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
