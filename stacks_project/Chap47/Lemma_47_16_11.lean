/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.MinimalPrime

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.16.11: if `p` is a minimal prime of a Noetherian local ring `A` with
`ringKrullDim (A ⧸ p.1) = e`, then the localization at `p` of degree-`i` homology of a
normalized dualizing complex `ω` is nontrivial exactly when `i = -(e : ℤ)`. -/
@[stacks 0A7V] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.localizedHomology_nontrivial_iff :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H)
      (p : minimalPrimes A) (e : ℕ)
      (hdim : ringKrullDim (A ⧸ p.1) = e) (i : ℤ),
      Nontrivial
        (LocalizedModule.AtPrime p.1
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) ↔
        i = -(e : ℤ))
