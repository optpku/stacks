module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Noetherian DVR criterion for separated morphisms of algebraic spaces

A locally of finite type quasi-separated morphism of algebraic spaces into a
locally Noetherian algebraic space is separated as soon as every DVR valuative
square has at most one lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- A locally of finite type quasi-separated morphism of algebraic spaces over a
scheme with locally Noetherian target is separated if every DVR valuative square
has at most one lift. -/
instance of_dvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.DVR.Uniqueness f] : Separated f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
