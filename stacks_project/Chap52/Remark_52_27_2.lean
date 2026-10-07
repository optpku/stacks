module

public import stacks_project.Chap52.Lemma_52_24_1
public import stacks_project.Chap52.Lemma_52_27_1
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTripleSetup

/-- Remark 52.27.2: the Picard-neighborhood extension conclusion of Lemma 52.27.1
holds for a Noetherian local ring with a dualizing complex when the finiteness
hypotheses are replaced by either the stated Serre/minimal-prime condition or the
primewise depth-dimension condition, while retaining `f`-adic completeness and the
vanishing of third local cohomology of `A / fA`. -/
@[stacks 0F2E]
theorem picardNeighborhoodRestriction_surjective_of_serreOrDepth
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    [IsAdicComplete (Ideal.span {f}) A]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
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
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))) :
    let S := CoherentTripleSetup.ofElement f hf_mem hf_regular
    let U₀ := Opens.toScheme S.algebraization.U₀
    let U := Opens.toScheme S.algebraization.U
    ∀ x : Scheme.PicardGroup U₀,
      ∃ (V : U.Opens)
        (j : U₀ ⟶ V.toScheme),
        j ≫ V.ι = S.closedFiberOnU ∧
          ∃ y : Scheme.PicardGroup V.toScheme,
            Scheme.Hom.picardPullback j y = x := sorry

end AlgebraicGeometry.CoherentTripleSetup
