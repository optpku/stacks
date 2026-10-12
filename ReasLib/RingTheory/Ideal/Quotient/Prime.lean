/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReasLib.RingTheory.Ideal.FiniteGeneration.PowerFamily

@[expose] public section

/-!
# Prime ideals in quotient rings

This leaf records the prime-complement comparison for the canonical quotient
map.  It is independent of any fiber construction and is intended for direct
use by localization arguments.
-/

universe u v

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- The prime of `A ⧸ I` induced by a prime `q` of `A` containing `I`. -/
def quotientOfLE (I : Ideal A) (q : PrimeSpectrum A) (hIq : I ≤ q.asIdeal) :
    PrimeSpectrum (A ⧸ I) :=
  ⟨Ideal.map (Ideal.Quotient.mk I) q.asIdeal,
    Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩

/-- The ideal underlying `quotientOfLE` is the image of the original prime. -/
@[simp]
theorem quotientOfLE_asIdeal (I : Ideal A) (q : PrimeSpectrum A)
    (hIq : I ≤ q.asIdeal) :
    (quotientOfLE I q hIq).asIdeal = Ideal.map (Ideal.Quotient.mk I) q.asIdeal := sorry

/-- The prime induced in a quotient contracts back to the original prime. -/
@[simp]
theorem quotientOfLE_comap (I : Ideal A) (q : PrimeSpectrum A)
    (hIq : I ≤ q.asIdeal) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) (quotientOfLE I q hIq) = q := sorry

/-- The ideal induced in a quotient contracts back to the original ideal. -/
@[simp]
theorem quotientOfLE_comap_asIdeal (I : Ideal A) (q : PrimeSpectrum A)
    (hIq : I ≤ q.asIdeal) :
    Ideal.comap (Ideal.Quotient.mk I) (quotientOfLE I q hIq).asIdeal = q.asIdeal := sorry

/-- The quotient map carries the complement of `q` to the complement of its
induced quotient prime. -/
theorem quotientOfLE_primeCompl (I : Ideal A) (q : PrimeSpectrum A)
    (hIq : I ≤ q.asIdeal) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.asIdeal.primeCompl =
      (quotientOfLE I q hIq).asIdeal.primeCompl := sorry

namespace PowerSpan

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The prime of the quotient by a mapped positive-power span induced by a
target prime containing all mapped generators. -/
@[stacks 07F8 "mapped power-span quotient prime"]
def quotient (f : R →+* S) (q : PrimeSpectrum S) {r : ℕ}
    (π : Fin r → R) (e : ℕ+) (hπ : ∀ i, f (π i) ∈ q.asIdeal) :
    PrimeSpectrum (S ⧸ Ideal.map f (Ideal.finPowerSpan π e)) :=
  PrimeSpectrum.quotientOfLE
    (Ideal.map f (Ideal.finPowerSpan π e)) q
    (Ideal.map_finPowerSpan_le f π e q.asIdeal hπ)

/-- The ideal underlying `PowerSpan.quotient` is the image of the original
prime in the positive-power quotient. -/
@[stacks 07F8 "power-span quotient prime ideal", simp]
theorem asIdeal (f : R →+* S) (q : PrimeSpectrum S) {r : ℕ}
    (π : Fin r → R) (e : ℕ+) (hπ : ∀ i, f (π i) ∈ q.asIdeal) :
    (quotient f q π e hπ).asIdeal =
      Ideal.map (Ideal.Quotient.mk (Ideal.map f (Ideal.finPowerSpan π e)))
        q.asIdeal := sorry

/-- Contracting the induced quotient prime along the quotient map recovers
the original prime. -/
@[stacks 07F8 "power-span quotient prime comap", simp]
theorem comap (f : R →+* S) (q : PrimeSpectrum S) {r : ℕ}
    (π : Fin r → R) (e : ℕ+) (hπ : ∀ i, f (π i) ∈ q.asIdeal) :
    PrimeSpectrum.comap
        (Ideal.Quotient.mk (Ideal.map f (Ideal.finPowerSpan π e)))
        (quotient f q π e hπ) = q := sorry

end PowerSpan

end PrimeSpectrum
