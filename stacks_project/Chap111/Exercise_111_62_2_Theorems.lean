module

public import ReasLib.RingTheory.Spectrum.Prime.Chevalley
public import ReasLib.RingTheory.Jacobson.FiniteType
public import ReasLib.RingTheory.NoetherNormalization
public import ReasLib.RingTheory.KrullDimension.FiniteType.FractionRing
public import ReasLib.RingTheory.RegularLocalRing.Domain
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.62.2 (Theorems) (1): Chevalley's theorem: a finite-presentation ring map
sends constructible sets in Spec S to constructible sets in Spec R. -/
@[stacks 0FWL] #check
  (PrimeSpectrum.isConstructible_comap_image_of_finitePresentation :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S},
      f.FinitePresentation →
        ∀ {s : Set (PrimeSpectrum S)}, Topology.IsConstructible s →
          Topology.IsConstructible (PrimeSpectrum.comap f '' s))

/- Exercise 111.62.2 (Theorems) (2): algebraic Hilbert Nullstellensatz: a finite-type algebra
over a Jacobson ring is Jacobson. -/
@[stacks 0FWL] #check
  (Algebra.FiniteType.isJacobsonRing :
    ∀ (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsJacobsonRing A] [Algebra.FiniteType A B], IsJacobsonRing B)

/- Exercise 111.62.2 (Theorems) (3): the Krull dimension of a finite-type domain over a
field equals the transcendence degree of its fraction field. -/
@[stacks 0FWL] #check
  (Algebra.FiniteType.ringKrullDim_eq_trdeg_fractionRing :
    ∀ {k : Type u} [Field k] {S : Type v} [CommRing S] [IsDomain S]
      [Algebra k S] [Algebra.FiniteType k S],
      ringKrullDim S = Cardinal.toNat (Algebra.trdeg k (FractionRing S)))

/- Exercise 111.62.2 (Theorems) (4): Noether normalization: a nontrivial finite-type algebra
over a field is finite over an injective polynomial subalgebra. -/
@[stacks 0FWL] #check
  (Algebra.exists_injective_finite_mvPolynomial :
    ∀ (field : Type u) (ring : Type v) [Field field] [CommRing ring] [Nontrivial ring]
      [Algebra field ring] [Algebra.FiniteType field ring],
      ∃ count, ∃ embedding : MvPolynomial (Fin count) field →ₐ[field] ring,
        Function.Injective embedding ∧ embedding.Finite)

/- Exercise 111.62.2 (Theorems) (5): a regular local ring is an integral domain. -/
@[stacks 0FWL] #check
  (IsRegularLocalRing.isDomain :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R], IsDomain R)
