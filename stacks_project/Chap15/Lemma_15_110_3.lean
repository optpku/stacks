module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.FlatLocal

/-!
# Lemma 15.110.3

@stack 0AW4
-/

@[expose] public section

universe u v

open TopologicalSpace

/- Lemma 15.110.3 (current Stacks numbering: Lemma 15.111.3, tag `0AW4`):
a flat local map with catenary equidimensional Noetherian target has
equidimensional prime quotients and a catenary equidimensional source. -/

/- Lemma 15.110.3 (1), tag `0AW4`: equidimensionality of every target quotient. -/
@[stacks 0AW4 "Lemma 15.110.3 (1)"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [Module.Flat A B] [IsCatenaryRing B]
    [EquidimensionalSpace (PrimeSpectrum B)] (p : PrimeSpectrum A) ↦
  (RingHom.Flat.Local.equidimensional_quotient
      (f := algebraMap A B) (RingHom.flat_algebraMap_iff.mpr inferInstance) p :
    EquidimensionalSpace
      (PrimeSpectrum (B ⧸ Ideal.map (algebraMap A B) p.asIdeal)))

/- Lemma 15.110.3 (2), tag `0AW4`: catenarity of the source spectrum. -/
@[stacks 0AW4 "Lemma 15.110.3 (2)"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [Module.Flat A B] [IsCatenaryRing B]
    [EquidimensionalSpace (PrimeSpectrum B)] ↦
  (RingHom.Flat.Local.catenarySpace
      (f := algebraMap A B) (RingHom.flat_algebraMap_iff.mpr inferInstance) :
    IsCatenaryRing A)

/- Lemma 15.110.3 (3), tag `0AW4`: equidimensionality of the source spectrum. -/
@[stacks 0AW4 "Lemma 15.110.3 (3)"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [Module.Flat A B] [IsCatenaryRing B]
    [EquidimensionalSpace (PrimeSpectrum B)] ↦
  (RingHom.Flat.Local.equidimensionalSpace
      (f := algebraMap A B) (RingHom.flat_algebraMap_iff.mpr inferInstance) :
    EquidimensionalSpace (PrimeSpectrum A))
