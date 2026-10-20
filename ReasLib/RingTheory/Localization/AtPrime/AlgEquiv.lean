module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Prime Localizations under Algebra Equivalences

This leaf gives the `PrimeSpectrum`-facing specialization of Mathlib's
`Localization.localAlgEquiv`.  The primitive theorem is formulated for an
explicit equality of ideals; an algebra equivalence canonically supplies that
equality at the prime obtained by contraction.
-/

@[expose] public section

universe u v w

namespace AlgEquiv

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- An `R`-algebra equivalence induces an `R`-algebra equivalence between the
local rings at a prime of its target and its contracted prime in the source. -/
noncomputable def localizationAtPrime (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

end AlgEquiv
