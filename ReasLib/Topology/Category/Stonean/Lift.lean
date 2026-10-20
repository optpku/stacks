module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Category.Stonean.Basic

/-!
# Stonean lifts along surjections

This module gives the explicit-surjectivity form of Mathlib's projective Stonean lift.  It keeps
the `Epi` conversion inside a named bridge, so callers with a map-level surjectivity hypothesis do
not need to alter local typeclass inference.
-/

@[expose] public section

universe u

open CategoryTheory Function

namespace CompHaus

/-- Lift a map from a Stonean space through a surjective map of compact Hausdorff spaces. -/
@[stacks 090D "Stonean lift along a surjection"]
noncomputable def liftOfSurjective {X Y : CompHaus.{u}} {Z : Stonean.{u}}
    (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) (hf : Surjective f) : Z.compHaus ⟶ X :=
  @CompHaus.lift X Y Z e f ((CompHaus.epi_iff_surjective f).2 hf)

/-- The explicit-surjectivity Stonean lift commutes with the map it lifts through. -/
@[reassoc]
theorem liftOfSurjective_lifts {X Y : CompHaus.{u}} {Z : Stonean.{u}}
    (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) (hf : Surjective f) :
    liftOfSurjective e f hf ≫ f = e := sorry

end CompHaus
