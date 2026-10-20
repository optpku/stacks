module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GlobalSections

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom.FiberSections
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsProper

/-- Every idempotent global section on a fiber of a proper scheme morphism lies in the range of
the canonical map from the corresponding pushforward stalk. -/
theorem idempotent_mem_range_fiberSections {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsProper f] (s : S)
    (e : Scheme.globalSectionsRing (f.fiber s)) (he : IsIdempotentElem e) :
    e ∈ (pushforwardStalkMap f s).range := sorry

end AlgebraicGeometry.IsProper

end
