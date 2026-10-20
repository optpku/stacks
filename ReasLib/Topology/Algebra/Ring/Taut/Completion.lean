module

public import ReasLib.Topology.Algebra.LinearTopology.Completion.Ring
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Tautness of the canonical completion map

The canonical map from a linearly topologized ring to its inverse-limit completion is taut.
-/

@[expose] public section

universe u

open IsLinearTopology

namespace RingHom

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The canonical map from a linearly topologized ring to its inverse-limit completion
is taut. -/
theorem IsTaut.completion : (Completion.coeRingHom : A →+* Completion A A).IsTaut :=
  sorry

end RingHom
