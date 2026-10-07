module

public import ReasLib.RingTheory.Spectrum.Prime.Profinite.Algebra
public import ReasLib.RingTheory.Algebraic.ResidueField
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits CommRingCat

universe u v

/- Lemma 61.5.6 (1): if primes of B lying over the same prime of A are
incomparable, then Spec(B) is profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_isAntichainOnFibers :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)],
      Algebra.IsAntichainOnFibers R S →
        IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (2): if A → B induces algebraic residue-field extensions, then
Spec(B) is profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_isAlgebraicOnResidueFields :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)],
      Algebra.IsAlgebraicOnResidueFields R S →
        IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (3): if A → B is a local isomorphism, then Spec(B) is
profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_isLocalIso :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.IsLocalIso R S],
      IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (4): if A → B identifies local rings, then Spec(B) is
profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_isIsoOnLocalRings :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)],
      (algebraMap R S).IsIsoOnLocalRings →
        IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (5): if A → B is weakly étale, then Spec(B) is profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_weaklyEtale :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.WeaklyEtale R S],
      IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (6): if A → B is quasi-finite, then Spec(B) is profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_quasiFinite :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.FiniteType R S]
      [Algebra.QuasiFinite R S],
      IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (7): if A → B is unramified, then Spec(B) is profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_unramified :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.Unramified R S],
      IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (8): if A → B is étale, then Spec(B) is profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_etale :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.Etale R S],
      IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)))

/- Lemma 61.5.6 (9): if B is a filtered colimit of A-algebras as in (1)–(8),
in the sense that each stage has profinite spectrum, then Spec(B) is
profinite. -/
@[stacks 0978] #check
  (PrimeSpectrum.isTotallyDisconnected_univ_of_isColimit :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      {J : Type v} [Category.{v} J] [IsFiltered J]
      (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
        (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
        (hF : ∀ j, IsTotallyDisconnected
          (Set.univ : Set (PrimeSpectrum (F.obj j).right))),
        IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum A)))
