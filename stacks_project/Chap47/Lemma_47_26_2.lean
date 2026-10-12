/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.26.2: under any of the stated syntomic, faithfully flat local complete
intersection, or faithfully flat finite-type Gorenstein-fibre hypotheses, a complex is
dualizing exactly when its derived extension of scalars is dualizing. -/
@[stacks 0E4D] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.iff_derivedExtensionOfScalars :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (φ : A →+* B),
      ((φ.Syntomic ∧ Function.Surjective (PrimeSpectrum.comap φ)) ∨
        (φ.FaithfullyFlat ∧ φ.IsLocalCompleteIntersection) ∨
        (φ.FaithfullyFlat ∧ φ.FiniteType ∧
          ∀ p : PrimeSpectrum A, IsGorensteinRing (φ.Fiber p.asIdeal))) →
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B))) →
      (K : DerivedCategory (ModuleCat.{u} A)) →
      K.IsDualizingComplex HA ↔
        ((ModuleCat.derivedExtensionOfScalars φ).obj K).IsDualizingComplex HB)
