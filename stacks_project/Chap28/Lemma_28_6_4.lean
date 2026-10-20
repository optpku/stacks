module

public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.IdealComplement
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.6.4 (1): the punctured spectrum of a Noetherian local ring is a
Jacobson scheme. -/
@[stacks 02IM] #check
  (AlgebraicGeometry.jacobsonSpace_puncturedSpectrum_of_isNoetherianRing :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      JacobsonSpace (AlgebraicGeometry.PuncturedSpectrum.scheme R))

/- The complement of the zero locus of the Jacobson radical of a Noetherian ring is a
Jacobson scheme. -/
#check
  (AlgebraicGeometry.jacobsonSpace_spec_compl_zeroLocus_ringJacobson :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
      JacobsonSpace
        (AlgebraicGeometry.Scheme.Opens.toScheme
          (⟨(PrimeSpectrum.zeroLocus ((Ring.jacobson R : Ideal R) : Set R))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ :
              (AlgebraicGeometry.Spec (.of R)).Opens)))

/- If an ideal of a Noetherian ring is contained in the Jacobson radical, then the
complement of its zero locus is a Jacobson scheme. -/
#check
  (AlgebraicGeometry.jacobsonSpace_spec_compl_zeroLocus_of_le_ringJacobson :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      (I : Ideal R) (_ : I ≤ Ring.jacobson R),
      JacobsonSpace
        (AlgebraicGeometry.Scheme.Opens.toScheme
          (⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ :
              (AlgebraicGeometry.Spec (.of R)).Opens)))
