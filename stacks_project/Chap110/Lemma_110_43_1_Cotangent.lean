module

public import ReasLib.RingTheory.CotangentComplex.Basic

@[expose] public section

universe u

#check (RingHom.cotangentComplex :
  ∀ {R S : Type u} [CommRing R] [CommRing S],
    (R →+* S) → CochainComplex (ModuleCat.{u} S) ℤ)
