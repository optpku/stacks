module

public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible Topology of Spectral Spaces

This module records separation, disconnectedness, and compactness properties
of the constructible topology on a spectral space.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

namespace Topology

/-- A constructible subset of a spectral space is clopen in its constructible
topology. -/
theorem IsConstructible.isClopen_constructibleTopology [SpectralSpace X]
    {s : Set X} (hs : IsConstructible s) :
    @IsClopen X (constructibleTopology X) s := sorry

/-- Constructible subsets of a spectral space are exactly the clopen subsets
for its constructible topology. -/
@[stacks 0901 "constructible subsets are patch clopen"]
theorem isConstructible_iff_isClopen_constructibleTopology [SpectralSpace X]
    {s : Set X} :
    IsConstructible s ↔ @IsClopen X (constructibleTopology X) s := sorry

end Topology

namespace WithConstructibleTopology

/-- The constructible topology of a spectral space is totally separated. -/
@[stacks 0901 "total separation"]
instance totallySeparatedSpace [SpectralSpace X] :
    TotallySeparatedSpace (WithConstructibleTopology X) := sorry

end WithConstructibleTopology

/-- The constructible topology of a spectral space is Hausdorff. -/
@[stacks 0901 "Hausdorffness"]
theorem constructibleTopology_t2Space [SpectralSpace X] :
    @T2Space X (constructibleTopology X) := sorry

/-- The constructible topology of a spectral space is totally disconnected. -/
@[stacks 0901 "total disconnectedness"]
theorem constructibleTopology_totallyDisconnectedSpace [SpectralSpace X] :
    @TotallyDisconnectedSpace X (constructibleTopology X) := sorry

/-- The constructible topology of a spectral space is compact. -/
@[stacks 0901 "compactness"]
theorem constructibleTopology_compactSpace [SpectralSpace X] :
    @CompactSpace X (constructibleTopology X) := sorry
