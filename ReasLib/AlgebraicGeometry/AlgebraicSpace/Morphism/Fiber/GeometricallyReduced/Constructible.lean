module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The geometrically reduced fibre locus of a quasi-compact morphism of algebraic spaces
locally of finite presentation is étale locally constructible. -/
@[stacks 0E0A]
theorem isEtaleLocallyConstructible_geometricallyReducedFiberLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] :
    IsEtaleLocallyConstructible (geometricallyReducedFiberLocus f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
