module

public import ReasLib.Topology.ConstructibleTopology.Spectral

/-!
# Spectral Maps and Constructible Topologies

This module records how a spectral map acts on constructible topologies and
constructible subsets.
-/

@[expose] public section

universe u v

open Set TopologicalSpace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

namespace IsSpectralMap

/-- A spectral map is continuous for constructible topologies. -/
@[stacks 0A2S "constructible-topology continuity"]
theorem continuous_constructibleTopology (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f := sorry

/-- A spectral map between spectral spaces pulls constructible subsets back to
constructible subsets. -/
theorem isConstructible_preimage [SpectralSpace X] [SpectralSpace Y]
    (hf : IsSpectralMap f) {s : Set Y} (hs : IsConstructible s) :
    IsConstructible (f ⁻¹' s) := sorry

/-- Every fiber of a spectral map between spectral spaces is compact. -/
@[stacks 0A2S "compact fibers"]
theorem isCompact_fiber [SpectralSpace X] [SpectralSpace Y]
    (hf : IsSpectralMap f) (y : Y) :
    IsCompact (f ⁻¹' ({y} : Set Y)) := sorry

/-- The range of a spectral map between spectral spaces is closed in the
constructible topology. -/
@[stacks 0A2S "constructibly closed range"]
theorem isClosed_range_constructibleTopology [SpectralSpace X] [SpectralSpace Y]
    (hf : IsSpectralMap f) :
    IsClosed[constructibleTopology Y] (range f) := sorry

end IsSpectralMap

namespace Continuous

/-- For spectral spaces, a continuous map is spectral exactly when it is
continuous for the constructible topologies. -/
@[stacks 0G1J]
theorem isSpectralMap_iff_constructibleTopology [SpectralSpace X] [SpectralSpace Y]
    (hf : Continuous f) :
    IsSpectralMap f ↔ Continuous[constructibleTopology X, constructibleTopology Y] f := sorry

end Continuous
