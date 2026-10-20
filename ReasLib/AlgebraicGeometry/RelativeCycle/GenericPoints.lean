module

public import ReasLib.AlgebraicGeometry.RelativeCycle
public import Mathlib.Topology.Sober

/-!
# Generic-point determination of relative cycles

Relative cycles over a locally Noetherian base are determined by their values
at the generic points of its irreducible components.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Two relative `r`-cycles for a locally finite type morphism over a locally Noetherian
scheme are equal exactly when their fibre cycles agree at every generic point of an
irreducible component of the base. -/
theorem eq_iff_eq_on_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {α β : f.FiberCycleFamily r} (hα : IsRelative α) (hβ : IsRelative β) :
    α = β ↔ ∀ η ∈ genericPoints S, α η = β η := sorry

end AlgebraicGeometry.RelativeCycle
