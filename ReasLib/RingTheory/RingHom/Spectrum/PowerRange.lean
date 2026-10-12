/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import ReasLib.RingTheory.RingHom.PowerImage.Surjective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral consequences of positive-power-surjective maps

This leaf contains only the spectrum-side consequence of the general
`RingHom.IsPowerSurjective` property.  The property and its integrality bridge are owned by
`RingHom.PowerImage.Surjective`.
-/

@[expose] public section

universe u v

namespace RingHom

namespace PowerRange

/-- A field-source map with positive powers in its range has subsingleton target spectrum. -/
theorem primeSpectrum_subsingleton_of_forall_pow_mem_range
    {K : Type u} {A : Type v} [Field K] [CommRing A] (f : K →+* A)
    (hpows : ∀ x : A, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ f.range) :
    Subsingleton (PrimeSpectrum A) := by
  constructor
  intro q₁ q₂
  ext x
  obtain ⟨n, hn, y, hy⟩ := hpows x
  rw [← q₁.2.pow_mem_iff_mem _ hn, ← q₂.2.pow_mem_iff_mem _ hn, ← hy]
  have hcomap : PrimeSpectrum.comap f q₁ = PrimeSpectrum.comap f q₂ :=
    Subsingleton.elim _ _
  rw [PrimeSpectrum.ext_iff, SetLike.ext_iff] at hcomap
  exact hcomap y

/-- The same spectrum criterion in terms of the reusable bundled predicate. -/
theorem primeSpectrum_subsingleton_of_isPowerSurjective
    {K : Type u} {A : Type v} [Field K] [CommRing A] (f : K →+* A)
    (hpow : f.IsPowerSurjective) :
    Subsingleton (PrimeSpectrum A) := by
  apply primeSpectrum_subsingleton_of_forall_pow_mem_range f
  intro x
  obtain ⟨e, he⟩ := hpow x
  exact ⟨e, e.pos, he⟩

end PowerRange

namespace IsPowerSurjective

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A positive-power-surjective ring map whose kernel is contained in the nilradical induces a
homeomorphism on prime spectra. -/
@[stacks 0BR8 "bundled positive-power-surjective spectral homeomorphism"]
theorem isHomeomorph_comap {f : R →+* S}
    (hpow : f.IsPowerSurjective) (hker : RingHom.ker f ≤ nilradical R) :
    IsHomeomorph (PrimeSpectrum.comap f) := by
  apply PrimeSpectrum.isHomeomorph_comap f ?_ hker
  intro x
  obtain ⟨e, he⟩ := hpow x
  exact ⟨e, e.pos, he⟩

end IsPowerSurjective

end RingHom
