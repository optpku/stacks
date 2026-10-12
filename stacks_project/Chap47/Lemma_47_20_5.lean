/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.RingLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.20.5 (1): for a Noetherian ring with a chosen dualizing complex,
the locus of primes whose local rings are Cohen–Macaulay is open. -/
@[stacks 0EHT] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.isOpen_cohenMacaulayRingLocus :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H),
      IsOpen (PrimeSpectrum.cohenMacaulayLocus A))

/- Lemma 47.20.5 (2): for a Noetherian ring with a chosen dualizing complex,
the locus of primes whose local rings are Cohen–Macaulay is dense. -/
@[stacks 0EHT] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.dense_cohenMacaulayRingLocus :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H),
      Dense (PrimeSpectrum.cohenMacaulayLocus A))

end CategoryTheory.DerivedCategory.IsDualizingComplex
