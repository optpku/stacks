module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Finite presentation of relative differentials

Relative differentials of a locally finitely presented scheme morphism form a finitely presented
module sheaf.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The relative differential sheaf of a locally finitely presented morphism of schemes is
finitely presented. -/
instance instIsFinitePresentationDifferentialsOfLocallyOfFinitePresentation
    (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    (Ω[f.toShHom]).IsFinitePresentation := sorry

end AlgebraicGeometry
