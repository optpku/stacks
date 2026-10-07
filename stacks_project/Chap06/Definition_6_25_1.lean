module

public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}}

/- Definition 6.25.1: a ringed space is the canonical mathlib owner `RingedSpace`, namely a
topological space equipped with a sheaf of commutative rings. -/
@[stacks 0091 "ringed spaces"]
#check RingedSpace

/- Definition 6.25.1 (morphisms): a morphism of ringed spaces is the canonical
`PresheafedSpace.Hom` pair consisting of a continuous map and a contravariant map of structure
sheaves. -/
@[stacks 0091 "continuous map with a sheaf map"]
#check @AlgebraicGeometry.PresheafedSpace.Hom

/- The structure-sheaf component has a named ringed-space-level owner, so callers can use the
canonical induced map without constructing the underlying pair by hand. -/
@[stacks 0091 "morphisms of ringed spaces"]
#check RingedSpace.Hom.commRingSheafPushforwardMap

end AlgebraicGeometry
