module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.NhdsKer
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import ReasLib.Topology.CompactOpen.Difference
public import ReasLib.Topology.Spectral.Limit.Spectral

/-!
# Compact-open intersections in spectral spaces

This module adds the spectral-space consequences of the generic compact-open intersection and
difference APIs. Their categorical cones live in `ReasLib.Topology.CompactOpen`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

section

variable [SpectralSpace X]

/-- Lemma 5.24.7 (1): the five standard presentations of a compact subset stable under
generalization are equivalent. -/
@[stacks 0A31 "five equivalent compact-generalizing presentations"]
theorem compactGeneralizingSubset_tfae (W : Set X) :
    List.TFAE
      [ (∃ T : Set (Set X), (∀ Z ∈ T, IsConstructible Z) ∧ W = ⋂₀ T) ∧
          StableUnderGeneralization W,
        IsCompact W ∧ StableUnderGeneralization W,
        ∃ E : Set X, IsCompact E ∧ W = nhdsKer E,
        ∃ S : Set (CompactOpens X), W = ⋂ U ∈ S, (U : Set X),
        ∃ S : Set (CompactOpens X), IsCompactOpenDirectedIntersection W S ] := sorry

namespace IsCompactOpenDirectedIntersection

/-- Lemma 5.24.7 (2): a nonempty directed compact-open intersection in a spectral space is
spectral. -/
@[stacks 0A31 "spectrality of the intersection"]
theorem spectralSpace
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) :
    SpectralSpace W := sorry

/-- Lemma 5.24.7 (4): every open neighbourhood of a directed compact-open intersection contains
one stage. -/
@[stacks 0A31 "a stage lies in every open neighborhood"]
theorem exists_compactOpen_subset_of_isOpen
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    {U : Set X} (hU : IsOpen U) (hWU : W ⊆ U) :
    ∃ V : CompactOpens X, V ∈ S ∧ (V : Set X) ⊆ U := sorry

end IsCompactOpenDirectedIntersection

namespace CompactOpens

/-- Removing a constructible subset from a compact open in a spectral space leaves a spectral
subspace. -/
@[stacks 0AP0 "compact-open constructible difference"]
theorem spectralSpace_sdiff_constructible
    (U : CompactOpens X) (E : Set X) (hE : IsConstructible E) :
    SpectralSpace ((U : Set X) \ E : Set X) := sorry

/-- Inclusion between two compact-open stage differences is a spectral map. -/
@[stacks 0AP0 "spectral compact-open difference inclusion"]
theorem isSpectralMap_sdiffInclusion
    (E : Set X) (hE : IsConstructible E)
    {U V : CompactOpens X} (hUV : U ≤ V) :
    IsSpectralMap (compactOpenSdiffInclusion E hUV) := sorry

end CompactOpens

end
