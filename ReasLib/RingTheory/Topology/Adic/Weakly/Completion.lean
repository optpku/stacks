module

public import ReasLib.RingTheory.Topology.Adic.Weakly.Characterization
public import ReasLib.Topology.Algebra.Ring.Taut.Completion

/-!
# Weak adicity of inverse-limit completions
-/

@[expose] public section

universe u

open IsLinearTopology

namespace TopologicalRing

variable {A : Type u} [CommRing A] [TopologicalSpace A]

namespace IsWeaklyAdicRing

/-- The inverse-limit completion of a weakly pre-adic ring is weakly adic. -/
instance instCompletion [IsWeaklyPreadicRing A] :
    IsWeaklyAdicRing (Completion A A) :=
  sorry

end IsWeaklyAdicRing

end TopologicalRing
