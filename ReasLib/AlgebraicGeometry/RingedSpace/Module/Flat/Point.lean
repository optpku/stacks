module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Skyscraper
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat point inclusions

The inclusion of a point equipped with the ambient stalk ring is a flat morphism of ringed
spaces.  This leaf keeps the reusable instance next to the point-ringed-space construction.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The canonical inclusion of a point with its stalk ring is flat. -/
@[stacks 02N3 "point inclusion", instance]
theorem pointInclusion_isFlat {X : RingedSpace.{u}} (x : X) :
    RingedSpace.Hom.IsFlat (pointInclusion x) := sorry

end AlgebraicGeometry
