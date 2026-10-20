module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Infinite open subsets of a local spectrum

This leaf owns the spectrum-level statement used by the Chapter 10 argument.  The open is kept as
the bundled `TopologicalSpace.Opens` object, while the conclusion deliberately exposes its point
set for direct use with `Set.Infinite`.
-/

@[expose] public section

universe u

open TopologicalSpace

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

/-- Lemma 10.61.1 (predicate owner; Stacks tag 02IG): if a Noetherian local domain does not have
Krull dimension at most one, every nonempty open subset of its spectrum is infinite. -/
@[stacks 02IG "non-one-dimensional local spectrum"]
theorem infinite_coe_of_ne_bot_of_not_krullDimLE_one
    (U : Opens (PrimeSpectrum R)) (hU : U ≠ ⊥)
    (hdim : ¬ Ring.KrullDimLE 1 R) :
    Set.Infinite (U : Set (PrimeSpectrum R)) := sorry

/-- Lemma 10.61.1 (canonical owner; Stacks tag 02IG): a nonempty open subset of the spectrum of a
Noetherian local domain of dimension at least two contains infinitely many prime ideals. -/
@[stacks 02IG "infinite nonempty open in a local spectrum"]
theorem infinite_coe_of_ne_bot_of_two_le_ringKrullDim
    (U : Opens (PrimeSpectrum R)) (hU : U ≠ ⊥)
    (hdim : 2 ≤ ringKrullDim R) :
    Set.Infinite (U : Set (PrimeSpectrum R)) := sorry

end PrimeSpectrum
