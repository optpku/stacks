/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Spectrum.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjectivity criteria for prime spectra

This leaf owns the contraction criteria for the map on prime spectra induced by a
commutative-ring homomorphism.  The source chapter uses an `algebraMap`; the reusable
owner takes an arbitrary `f : R →+* S`, while tensor-product base change remains in
`Spectrum.BaseChange`.

The pairwise bridges are intentionally exposed beside the source-facing TFAE.  A
downstream proof can use the spectral, prime-ideal, or radical-ideal view directly
without indexing into a `List.TFAE` proof.

@stack 00FI
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Surjectivity of `Spec(S) → Spec(R)` is equivalent to contraction of every extended prime
ideal back to itself. -/
@[stacks 00FI "surjective spectrum and prime contraction"]
theorem comap_surjective_iff_prime_contraction (f : R →+* S) :
    Function.Surjective (comap f) ↔
      ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal := sorry

/-- The prime-contraction condition is equivalent to contraction of every radical ideal after
extension.  This is the source TFAE bridge from clause (4) to clause (3). -/
@[stacks 00FI "prime contraction and radical ideal contraction"]
theorem prime_contraction_iff_radicalIdeal_contraction (f : R →+* S) :
    (∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal) ↔
      ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I := sorry

/-- Contraction of the radical of every extended ideal is equivalent to the prime-contraction
condition.  This is the source TFAE bridge from clause (2) to clause (4). -/
@[stacks 00FI "radical contraction and prime contraction"]
theorem radical_map_comap_iff_prime_contraction (f : R →+* S) :
    (∀ I : Ideal R, ((I.map f).radical).comap f = I.radical) ↔
      ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal := sorry

/-- Lemma 10.30.3 (Tag 00FI): the four equivalent criteria for surjectivity of the map on prime
spectra induced by a ring homomorphism. -/
@[stacks 00FI "surjectivity criteria for prime spectra"]
theorem comap_surjective_tfae (f : R →+* S) :
    List.TFAE
      [ Function.Surjective (comap f),
        ∀ I : Ideal R, ((I.map f).radical).comap f = I.radical,
        ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I,
        ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal ] := sorry

end PrimeSpectrum
