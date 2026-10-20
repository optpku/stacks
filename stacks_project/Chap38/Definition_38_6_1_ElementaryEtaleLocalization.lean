module

public import ReasLib.RingTheory.Etale.ElementaryLocalization

universe u v w x

#check (RingHom.ElementaryEtaleLocalization.{u, v, w, x} :
  {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    (f : R →+* S) → (p : PrimeSpectrum R) → (q : PrimeSpectrum S) →
      p.asIdeal = q.asIdeal.comap f →
        Type (max (max (max u v) (w + 1)) (x + 1)))
