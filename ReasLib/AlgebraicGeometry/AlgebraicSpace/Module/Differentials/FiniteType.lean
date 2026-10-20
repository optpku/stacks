module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative differential sheaf of a locally finite type morphism of algebraic spaces
over a scheme is a finite-type module sheaf on the source. -/
instance isFiniteType_relativeDifferentials_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFiniteType f] :
    (Ω[f]).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
