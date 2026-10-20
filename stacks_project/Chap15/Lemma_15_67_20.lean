module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
import StacksCheckRecall

@[expose] public section

/-!
@stack 0H75

Lemma 15.67.20 is recalled from the explicit ring-homomorphism criterion for Tor-amplitude across
a surjective nilpotent thickening.  Derived extension of scalars is the canonical formalization of
the source's derived tensor base change.
-/

open CategoryTheory

universe u

/- Lemma 15.67.20 (0H75): Tor-amplitude in `[a,b]` is invariant under derived extension along a
surjective ring homomorphism with nilpotent kernel. -/
@[stacks 0H75 "Tor-amplitude across a nilpotent quotient"]
#check fun {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (hker : IsNilpotent (RingHom.ker σ))
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) ↦
  (DerivedCategory.HasTorAmplitudeIn.extension_iff_of_surjective_of_nilpotent_ker
      σ hσ hker K a b :
    DerivedCategory.HasTorAmplitudeIn (R := S)
        ((ModuleCat.derivedExtensionOfScalars σ).obj K) a b ↔
      DerivedCategory.HasTorAmplitudeIn (R := R) K a b)

/- The same nilpotent-thickening criterion for finite Tor dimension. -/
#check fun {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (hker : IsNilpotent (RingHom.ker σ)) (K : DerivedCategory (ModuleCat R)) ↦
  (DerivedCategory.HasFiniteTorDimension.extension_iff_of_surjective_of_nilpotent_ker
      σ hσ hker K :
    DerivedCategory.HasFiniteTorDimension (R := S)
        ((ModuleCat.derivedExtensionOfScalars σ).obj K) ↔
      DerivedCategory.HasFiniteTorDimension (R := R) K)
