module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalDepth
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.20.1 (1): the principal depth-dimension hypotheses imply canonical
extension of the coherent formal module. -/
@[stacks 0DXU] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_principal_depth :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] → [IsLocalRing A] →
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] →
      (S : AffineAlgebraizationSetup A) →
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H) →
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) →
      (f : A) →
      S.a = IsLocalRing.maximalIdeal A →
      S.I = Ideal.span ({f} : Set A) →
      f ∈ IsLocalRing.maximalIdeal A →
      IsRegular f →
      (∀ n : ℕ, IsFiniteLocallyFreeStage F n) →
      (∀ p : PrimeSpectrum A,
        p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          p ≠ IsLocalRing.closedPoint A →
            (.some (1 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal
                  (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
                WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal)) →
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (.some (3 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal)) →
      CanonicallyExtends S F)

/- Lemma 52.20.1 (2): in the complete-local case, the formal module lies in the
coherent-completion essential image. -/
@[stacks 0DXU] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_principal_depth :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      [IsCompleteLocalRing A] →
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] →
      (S : AffineAlgebraizationSetup A) →
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H) →
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) →
      (f : A) →
      S.a = IsLocalRing.maximalIdeal A →
      S.I = Ideal.span ({f} : Set A) →
      f ∈ IsLocalRing.maximalIdeal A →
      IsRegular f →
      (∀ n : ℕ, IsFiniteLocallyFreeStage F n) →
      (∀ p : PrimeSpectrum A,
        p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          p ≠ IsLocalRing.closedPoint A →
            (.some (1 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal
                  (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
                WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal)) →
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (.some (3 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal)) →
      (CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
