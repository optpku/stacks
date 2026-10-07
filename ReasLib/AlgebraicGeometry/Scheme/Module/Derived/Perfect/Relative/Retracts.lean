module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Retracts
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.Retract.InverseImage
public import ReasLib.CategoryTheory.ObjectProperty.Retract.Lattice

@[expose] public section

/-!
# Retracts of relatively perfect derived modules on schemes

Relative perfectness for flat, locally finitely presented scheme morphisms is stable under
retracts in the derived category of modules.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- The objects perfect relative to a flat, locally finitely presented scheme morphism are
stable under retracts. -/
instance perfectRelativeTo_isStableUnderRetracts (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty.IsStableUnderRetracts (perfectRelativeTo f) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
