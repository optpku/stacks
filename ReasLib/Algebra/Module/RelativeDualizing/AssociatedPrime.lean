module

public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange.Bijective
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization

@[expose] public section

open AlgebraicGeometry

universe u v

namespace Algebra.RelativeDualizingModule

/-- For a quasi-finite map of Noetherian rings, the associated primes of its
relative dualizing module are exactly the primes lying over associated primes of
the base ring. -/
theorem associatedPrimes_eq_liesOver
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    { q : PrimeSpectrum B |
        q.asIdeal ∈ associatedPrimesOfModule B
          (of A B' B h_quasiFinite h_open) } =
      { q : PrimeSpectrum B |
        q.asIdeal.under A ∈ associatedPrimesOfModule A A } := sorry

end Algebra.RelativeDualizingModule
