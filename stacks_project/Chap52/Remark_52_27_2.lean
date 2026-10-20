module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard.SerreDepth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Remark 52.27.2: the Picard-neighborhood extension conclusion of Lemma 52.27.1
holds for a Noetherian local ring with a dualizing complex when the finiteness
hypotheses are replaced by either the stated Serre/minimal-prime condition or the
primewise depth-dimension condition, while retaining `f`-adic completeness and the
vanishing of third local cohomology of `A / fA`. -/
@[stacks 0F2E] #check
  (AlgebraicGeometry.PuncturedSpectrum.picardNeighborhoodRestriction_surjective_of_serreOrDepth :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    [IsAdicComplete (Ideal.span {f}) A]
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    (h_alternative :
      (SerreConditionS (Localization.Away f) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            f ∉ p.asIdeal →
              (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ({f} : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus ({f} : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal))))
    (h_h3 : IsZero
      ((localCohomology (IsLocalRing.maximalIdeal A) 3).obj
        (ModuleCat.of A
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))),
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A
    let closedFiber := (quotientMap ⁻¹ᵁ punctured).toScheme
    ∀ x : Scheme.PicardGroup closedFiber,
      ∃ (V : punctured.toScheme.Opens)
        (j : closedFiber ⟶ V.toScheme),
        j ≫ V.ι = quotientMap ∣_ punctured ∧
          ∃ y : Scheme.PicardGroup V.toScheme,
            Scheme.Hom.picardPullback j y = x)
