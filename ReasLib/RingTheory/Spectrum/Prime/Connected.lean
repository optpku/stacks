/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Order.Hom.Esakia
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Connectedness of Prime Spectra

@stack 00EF
@stack 037S

This leaf owns the idempotent criterion for connectedness of the spectrum of a
nontrivial commutative ring.  It is stated in the `PrimeSpectrum` namespace so
that ring-level consumers do not depend on a chapter theorem or on a
source-specific wrapper name.
-/

@[expose] public section

open PrimeSpectrum TopologicalSpace

universe u v

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [Nontrivial R]

/-- Lemma 10.21.4 (Tag 00EF): a nontrivial commutative ring has connected prime
spectrum exactly when all of its idempotents are trivial. -/
@[stacks 00EF "idempotent criterion for connected prime spectra"]
theorem connectedSpace_iff_idempotents_trivial :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := sorry

end PrimeSpectrum

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- A connected prime spectrum is nonempty, hence its ring is nontrivial. -/
@[stacks 037S "connected spectrum is nontrivial"]
theorem nontrivial_of_connected
    (h : ConnectedSpace (PrimeSpectrum R)) : Nontrivial R := sorry

/-- Connectedness of prime spectra descends along an injective ring homomorphism. -/
@[stacks 037S "injective spectrum descent"]
theorem connected_of_injective
    {S : Type v} [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum R) := sorry

end PrimeSpectrum
