module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.DerivedCompletion.Annihilator

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.9.1: over a Noetherian local ring with a dualizing complex, if
`cd(A, I) ≤ d` and the depth of `M` at `p` plus `dim(A ⧸ p)` is greater than
`d + s`, then an element outside `p` annihilates every cohomology module through
degree `s` of the derived `I`-adic completion of `RΓ_m(M)`. -/
@[stacks 0DXK] #check (Ideal.LocalCohomology.exists_commonAnnihilator_maximalIdeal :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (s d : ℤ)
    (h_cd : HasDimensionLE I d)
    (h_depth : ((d + s : ℤ) : EInt) <
      ((WithTop.map Int.ofNat
        (moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat) (ringKrullDim (A ⧸ p.asIdeal))),
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.derivedCompletionOf I I.fg_of_isNoetherianRing
            ((ModuleCat.SupportedOn.derivedInclusion
              (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A))).obj
                ((ModuleCat.SupportedOn.derivedSections
                  (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A))).obj
                    (ModuleCat.single0 (ModuleCat.of A M)))))))

end Ideal.LocalCohomology
