module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDifferentials

/-- The relative differential sheaf of a locally finitely presented morphism of algebraic
spaces over a scheme is a finitely presented module sheaf on the source. -/
instance isFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFinitePresentation f] :
    (Ω[f]).IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDifferentials
