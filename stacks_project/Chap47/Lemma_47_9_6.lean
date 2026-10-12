/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.SpectralSequence
public import ReasLib.RingTheory.Spectrum.Prime.ZeroLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.9.6 (1): for finitely generated ideals `I` and `J`, the intersection of their
zero loci is the zero locus of `I ⊔ J`. -/
@[stacks 0BJC] #check
  (PrimeSpectrum.zeroLocus_inter_of_fg :
    ∀ {A : Type u} [CommRing A] (I J : Ideal A), I.FG → J.FG →
      PrimeSpectrum.zeroLocus I ∩ PrimeSpectrum.zeroLocus J =
        PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))

/- Lemma 47.9.6 (2): the comparison from applying support in `I` and then in `J` to support
in `I ⊔ J` is an isomorphism. -/
@[stacks 0BJC] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.iteratedToSum_isIso :
    ∀ {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
      (RΓI : DerivedCategory (ModuleCat A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion I)
      (RΓJ : DerivedCategory (ModuleCat A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion J)
      (RΓIJ : DerivedCategory (ModuleCat A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion (I ⊔ J))
      (hRΓI : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓI)
      (hRΓJ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion J ⊣ RΓJ)
      (hRΓIJ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ),
      IsIso
        (CategoryTheory.DerivedCategory.LocalCohomology.iteratedToSum
          I J hI hJ RΓI RΓJ RΓIJ hRΓI hRΓJ hRΓIJ))

/- Lemma 47.9.6 (3): every bounded-below derived module admits the Grothendieck spectral
sequence for successive support in `I` and `J`, abutting to support in `I ⊔ J`. -/
@[stacks 0BJC] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.existsSpectralSequence :
    ∀ {A : Type u} [CommRing A] (I J : Ideal A), I.FG → J.FG →
      ∀ K : DerivedCategory.Plus (ModuleCat A),
        Nonempty
          (CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence
            (CategoryTheory.ModuleCat.IdealPowerTorsion.sectionsWithSupport J)
            (CategoryTheory.Functor.RightDerived.Bounded.functor
              (CategoryTheory.ModuleCat.IdealPowerTorsion.sectionsWithSupport I))
            (CategoryTheory.Functor.RightDerived.Bounded.functor
            (CategoryTheory.ModuleCat.IdealPowerTorsion.sectionsWithSupport (I ⊔ J))) K))
