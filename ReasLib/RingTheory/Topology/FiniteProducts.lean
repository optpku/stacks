module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Finite products of topological rings

Finite products preserve weak admissibility, countable indexing, and adicity.
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- Finite products of weakly admissible rings are weakly admissible. -/
instance instIsWeaklyAdmissibleRingPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsWeaklyAdmissibleRing (A i)] :
    IsWeaklyAdmissibleRing (∀ i, A i) := sorry

/-- Finite products of countably indexed rings are countably indexed. -/
instance instIsCountablyIndexedPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsCountablyIndexed (A i)] :
    IsCountablyIndexed (∀ i, A i) := sorry

/-- Finite products of adic rings are adic. -/
instance instIsAdicRingPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsAdicRing (A i)] :
    IsAdicRing (∀ i, A i) := sorry

end TopologicalRing
