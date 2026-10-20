module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.RelativeStrictTransform
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat
open Algebra.TensorProduct
open scoped AffineBlowupChart PrimeSpectrum TensorProduct

noncomputable section

universe u v

/- Lemma 38.30.2: a finite module whose localization away from `f` has rank `r` at every
extended base prime becomes free of rank `r` on a principal neighbourhood of every extended
base prime after a suitable finitely generated blowup. -/
@[stacks 0810] #check
  (AffineBlowupChart.RelativeStrictTransform.existsCenterFreeOfRank :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (f : R) (r : ℕ)
    {M : Type v} [AddCommGroup M] [Module S M] [Module.Finite S M]
    [Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    (_ : ∀ (p : PrimeSpectrum R) (_ : f ∉ p.asIdeal),
      Nonempty
        (LocalizedModule.AtPrime (Ideal.map (algebraMap R S) p.asIdeal) M ≃ₗ[Localization.AtPrime
          (Ideal.map (algebraMap R S) p.asIdeal)]
          (Fin r → Localization.AtPrime (Ideal.map (algebraMap R S) p.asIdeal)))),
    ∃ I : Ideal R,
      I.FG ∧
      V(({f} : Set R)) = V((I : Set R)) ∧
      ∀ a : I,
        let R' := R[I / a]
        let S' := S ⊗[R] R'
        let M' := AffineBlowupChart.relativeStrictTransform S I a M
        ∀ p' : PrimeSpectrum R',
          ∃ g : S',
            g ∉ Ideal.map includeRight.toRingHom p'.asIdeal ∧
            Nonempty
              (LocalizedModule.Away g M' ≃ₗ[Localization.Away g]
                (Fin r → Localization.Away g)))
