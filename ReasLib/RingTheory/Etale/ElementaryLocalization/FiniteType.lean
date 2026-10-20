module

public import ReasLib.RingTheory.Etale.ElementaryLocalization

/-!
# Finite-type maps in elementary étale localizations
-/

@[expose] public section

universe u v w x

namespace RingHom.ElementaryEtaleLocalization

/-- The right vertical map in an elementary étale localization is of finite type when
the original ring map is of finite type. -/
theorem right_finiteType {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    {hq : p.asIdeal = q.asIdeal.comap f}
    (L : RingHom.ElementaryEtaleLocalization.{u, v, w, x} f p q hq)
    (hf : f.FiniteType) :
    L.right.FiniteType := sorry

end RingHom.ElementaryEtaleLocalization
