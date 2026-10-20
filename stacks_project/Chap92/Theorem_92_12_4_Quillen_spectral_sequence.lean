module

public import ReasLib.Algebra.PolynomialSite.QuillenSpectralSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CategoryHomology

universe u

/- Theorem 92.12.4 (Quillen spectral sequence). A surjective map of commutative rings
admits a spectral sequence with symmetric-power differential-sheaf homology on its
first page and convergence to the derived self-tensor Tor abutment. -/
@[stacks 08RF] #check
  (Algebra.CotangentComplex.QuillenSpectralSequence.exists_spectralSequence :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)],
      Function.Surjective (algebraMap A B) →
        ∃ E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0,
          Algebra.CotangentComplex.QuillenSpectralSequence.IsQuillen A B E)

#check
  (Algebra.CotangentComplex.QuillenSpectralSequence.omegaSheaf_symmetricPower_isZero_of_lt :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)],
      Function.Surjective (algebraMap A B) → ∀ (k : ℕ) {i : ℕ}, i < k →
        IsZero (moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B k) i))
