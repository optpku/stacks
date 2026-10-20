module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DiscreteFieldFibers
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Local quasi-finiteness and discrete field fibers

For locally finite-type morphisms of algebraic spaces, local quasi-finiteness
is characterized by discreteness of scheme-theoretic field fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite-type morphism of algebraic spaces is locally quasi-finite
if and only if every scheme-theoretic field fiber has discrete space of points. -/
theorem locallyQuasiFinite_iff_discreteFieldFibers
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ discreteFieldFibers f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
