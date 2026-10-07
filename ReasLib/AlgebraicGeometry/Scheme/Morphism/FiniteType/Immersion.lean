module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Immersions of finite type

This module records the finite-type consequence of a closed immersion.  The local finite-type
component is already supplied by mathlib for every immersion; quasi-compactness upgrades a closed
immersion to the project-level `Scheme.Hom.FiniteType` class.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed immersion of schemes is of finite type. -/
@[stacks 01T6]
theorem finiteType_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    FiniteType f := sorry

/-- A closed immersion of schemes is canonically a finite-type morphism. -/
@[stacks 01T6, instance]
instance instFiniteTypeOfIsClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    FiniteType f := sorry

end AlgebraicGeometry.Scheme.Hom
