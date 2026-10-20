module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Constructible.FiniteUnion
public import ReasLib.Topology.Noetherian.Compactness

/-!
# Constructible Sets in Noetherian Spaces

This leaf records the finite locally closed description and continuous
pullback stability that arise from Noetherianity.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

namespace Topology

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.16.1: in a Noetherian space, constructible subsets are exactly
finite unions of locally closed subsets. -/
@[stacks 005L]
theorem isConstructible_iff_isFiniteUnionOfLocallyClosed_of_noetherian
    [NoetherianSpace X] {E : Set X} :
    IsConstructible E ↔ IsFiniteUnionOfLocallyClosed E := sorry

namespace IsConstructible

variable {Y : Type v} [TopologicalSpace Y] [NoetherianSpace X] {f : X → Y}

/-- Lemma 5.16.2: a continuous map from a Noetherian space pulls back
constructible subsets. -/
@[stacks 053Y]
theorem preimage_of_continuous_of_noetherianSpace
    {E : Set Y} (hE : IsConstructible E) (hf : Continuous f) :
    IsConstructible (f ⁻¹' E) := sorry

end IsConstructible

end Topology
