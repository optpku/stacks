/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.NormalizationDegree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.17.2: if `A → B` is surjective and the dualizing complex over `B` is
`RHom_A(B, ω)`, its normalization-degree function is the restriction of that of `ω`
along `PrimeSpectrum.comap`. -/
@[stacks 0A7Y]
#check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.normalizationDegreeFunction_coextensionOfSurjective :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))],
      (f : A →+* B) → Function.Surjective f →
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B))) →
      (ω : DerivedCategory (ModuleCat.{u} A)) →
      ω.IsDualizingComplex HA →
      (δA : PrimeSpectrum A → ℤ) →
      (δB : PrimeSpectrum B → ℤ) →
      IsNormalizationDegreeFunction ω δA →
      IsNormalizationDegreeFunction
        ((ModuleCat.derivedCoextensionOfScalars f).obj ω) δB →
      δB = δA ∘ _root_.PrimeSpectrum.comap f)

end CategoryTheory.DerivedCategory.IsDualizingComplex
