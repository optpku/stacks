/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Constructible.Neighborhood
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Open subsets of prime spectra

This file specializes the irreducible-closed openness criterion to closures of
points in a prime spectrum.  The result applies to any subset stable under
generalization, independently of regularity conditions.

@stack 07P8
-/

universe u

open PrimeSpectrum
open scoped PrimeSpectrum

namespace PrimeSpectrum

/-- A subset of a Noetherian prime spectrum that is stable under generalization is open exactly
when its trace on the closure of each of its points contains a nonempty ambient-open trace. -/
@[stacks 07P8 "Noetherian prime-spectrum openness criterion"]
theorem isOpen_iff_forall_mem_zeroLocus_contains_nonempty_open
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : Set (PrimeSpectrum R)) (hE : StableUnderGeneralization E) :
    IsOpen E ↔
      ∀ p ∈ E,
        ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
          U ∩ zeroLocus p.asIdeal ⊆ E := sorry

end PrimeSpectrum
