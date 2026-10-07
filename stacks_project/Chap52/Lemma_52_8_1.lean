module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.DerivedCompletion.Annihilator

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.8.1 -/
@[stacks 0EFH] #check (Ideal.LocalCohomology.exists_commonAnnihilator_derivedCompletion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (h_dualizing :
        ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
      (I J : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (p : PrimeSpectrum A) (s d : ℤ)
      (h_not_mem : p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))
      (h_cd : HasDimensionLE I d)
      (h_depth : ∀ p' q : PrimeSpectrum A,
        p'.asIdeal ≤ p.asIdeal →
          q ∈ (PrimeSpectrum.zeroLocus (p'.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩
              PrimeSpectrum.zeroLocus (I : Set A) →
            ((d + s : ℤ) : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p'.asIdeal)
                  (LocalizedModule.AtPrime p'.asIdeal M)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p'.asIdeal.quotientAtPrime q))),
      ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
        f ∈ Module.annihilator A
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (DerivedCategory.derivedCompletionOf I I.fg_of_isNoetherianRing
              ((ModuleCat.SupportedOn.derivedInclusion
                (PrimeSpectrum.zeroLocus (J : Set A))).obj
                  ((ModuleCat.SupportedOn.derivedSections
                    (PrimeSpectrum.zeroLocus (J : Set A))).obj
                      (ModuleCat.single0 (ModuleCat.of A M)))))))

end Ideal.LocalCohomology
