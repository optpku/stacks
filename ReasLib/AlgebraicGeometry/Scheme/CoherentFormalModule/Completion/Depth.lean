/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.LocalCohomology
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Annihilator

@[expose] public section

open CategoryTheory
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

open CoherentCompletion

/-- For a Noetherian `(f)`-adically complete ring admitting a dualizing complex, if
the localized depth-plus-dimension bound is greater than `2` along the relevant
prime chains, completion on the complement of `V(𝔞)` is fully faithful on finite
locally free coherent modules. -/
theorem completionFullyFaithful_of_dualizingComplex_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    [IsAdicComplete (Ideal.span {f}) A]
    (h_depth : ∀ p q : PrimeSpectrum A,
      f ∉ p.asIdeal →
        q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (𝔞 : Set A) →
          (.some (2 : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
                ringKrullDim (p.asIdeal.quotientAtPrime q)) :
    let U := idealComplementOpens 𝔞
    Nonempty (onFiniteLocallyFree
      ((idealSheafDataOfIdealOnSpec (Ideal.span {f})).comap U.ι)).FullyFaithful := sorry

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
