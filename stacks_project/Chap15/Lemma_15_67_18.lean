module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.67.18

@stack 0DJF

The relative faithfully-flat Tor-amplitude equivalence is owned by the scalar-extension leaf.
-/

open CategoryTheory

universe u

/- Lemma 15.67.18: faithfully flat base change preserves Tor-amplitude measured over `R`. -/
@[stacks 0DJF "Lemma 15.67.18"]
#check fun {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (K : DerivedCategory (ModuleCat A)) (a b : ℤ)
    (hσ : (algebraMap A B).FaithfullyFlat) ↦
  (DerivedCategory.HasTorAmplitudeIn.iff_of_faithfullyFlat_baseChange K a b hσ :
    DerivedCategory.HasTorAmplitudeIn (R := R)
        (((ModuleCat.RestrictScalars.exact (algebraMap R A)).mapDerivedCategory).obj K) a b ↔
      DerivedCategory.HasTorAmplitudeIn (R := R)
        (((ModuleCat.RestrictScalars.exact (algebraMap R B)).mapDerivedCategory).obj
          ((ModuleCat.derivedExtensionOfScalars (algebraMap A B)).obj K)) a b)
