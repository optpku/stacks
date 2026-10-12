/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.ElementaryLocalization

universe u v w x

#check (RingHom.ElementaryEtaleLocalization.{u, v, w, x} :
  {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    (f : R →+* S) → (p : PrimeSpectrum R) → (q : PrimeSpectrum S) →
      p.asIdeal = q.asIdeal.comap f →
        Type (max (max (max u v) (w + 1)) (x + 1)))
