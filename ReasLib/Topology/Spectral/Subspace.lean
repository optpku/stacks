/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConstructibleTopology.Spectral

/-!
# Constructibly Closed Subspaces of Spectral Spaces

The constructibly closed subspace operation is the natural subtype-level
closure property for spectral spaces.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

namespace IsClosed

/-- A constructibly closed subspace of a spectral space is
spectral. -/
@[stacks 0902]
theorem spectralSpace_subtype_of_constructibleTopology
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) :
    SpectralSpace E := sorry

end IsClosed
