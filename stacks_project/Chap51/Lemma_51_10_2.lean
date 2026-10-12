/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Annihilator
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace Module.LocalCohomology

/- Lemma 51.10.2 -/
@[stacks 0EFE] #check (CategoryTheory.ModuleCat.SupportedOn.exists_annihilator_not_mem :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
      (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (p : PrimeSpectrum A) (s : ℕ)
      (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
      (hdepth : (∀ p' q : PrimeSpectrum A,
        p'.asIdeal ≤ p.asIdeal → q ∈ PrimeSpectrum.zeroLocus (I : Set A) →
          p'.asIdeal ≤ q.asIdeal →
            (.some (s : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p'.asIdeal)
                (LocalizedModule.AtPrime p'.asIdeal M)) : WithBot ℕ∞) +
                  ringKrullDim (p'.asIdeal.quotientAtPrime q))),
      ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℕ, i ≤ s →
        f ∈ Module.annihilator A
          (ModuleCat.SupportedOn.cohomology (PrimeSpectrum.zeroLocus (I : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)))

end Module.LocalCohomology
