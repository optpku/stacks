/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Depth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

/- Lemma 52.15.6 -/
@[stacks 0EKT] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.completionFullyFaithful_of_dualizingComplex_depth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
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
                  ringKrullDim (p.asIdeal.quotientAtPrime q)),
      let U := idealComplementOpens 𝔞
      Nonempty (CoherentCompletion.onFiniteLocallyFree
        ((idealSheafDataOfIdealOnSpec (Ideal.span {f})).comap U.ι)).FullyFaithful)

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
