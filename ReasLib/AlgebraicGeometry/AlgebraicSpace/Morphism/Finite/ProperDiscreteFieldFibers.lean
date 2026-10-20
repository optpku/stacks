module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DiscreteFieldFibers

/-!
# Finite morphisms and discrete field fibers

Over a locally Noetherian target, finite morphisms of algebraic spaces are
exactly the proper morphisms with discrete field fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFinite

/-- A morphism of algebraic spaces over a locally Noetherian target is finite
if and only if it is proper and every field fiber has discrete space of points. -/
theorem iff_proper_and_discreteFieldFibers_of_isLocallyNoetherian
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) : IsFinite f ↔ Proper f ∧ discreteFieldFibers f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFinite
