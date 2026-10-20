module

public import ReasLib.RingTheory.CohenMacaulay.Regular
public import ReasLib.RingTheory.CohenMacaulay.Module.AssociatedPrime
public import ReasLib.RingTheory.KrullDimension.FiniteType.FractionRing
public import ReasLib.RingTheory.Spectrum.Prime.Chevalley
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.58.2 (Theorems) (1): a regular ring is Cohen–Macaulay. -/
@[stacks 0D5H] #check
  (CohenMacaulayRing.of_isRegularRing :
    ∀ {R : Type u} [CommRing R], IsRegularRing R → CohenMacaulayRing R)

/- Exercise 111.58.2 (Theorems) (2): an associated prime of a Cohen–Macaulay module has
the full support dimension. -/
@[stacks 0D5H] #check
  (Module.CohenMacaulay.quotientDim_eq_supportDim_of_associatedPrime :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]
      (p : Ideal R), p ∈ associatedPrimes R M →
        ringKrullDim (R ⧸ p) = Module.supportDim R M)

/- Exercise 111.58.2 (Theorems) (3): the Krull dimension of a finite-type domain over a
field equals the transcendence degree of its fraction field. -/
@[stacks 0D5H] #check
  (Algebra.FiniteType.ringKrullDim_eq_trdeg_fractionRing :
    ∀ {k : Type u} [Field k] {S : Type v} [CommRing S] [IsDomain S]
      [Algebra k S] [Algebra.FiniteType k S],
      ringKrullDim S = Cardinal.toNat (Algebra.trdeg k (FractionRing S)))

/- Exercise 111.58.2 (Theorems) (4): Chevalley's theorem: a finite-presentation ring map
sends constructible sets in Spec S to constructible sets in Spec R. -/
@[stacks 0D5H] #check
  (PrimeSpectrum.isConstructible_comap_image_of_finitePresentation :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S},
      f.FinitePresentation →
        ∀ {s : Set (PrimeSpectrum S)}, Topology.IsConstructible s →
          Topology.IsConstructible (PrimeSpectrum.comap f '' s))
