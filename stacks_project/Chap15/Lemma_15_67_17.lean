module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.67.17

@stack 068S

The faithfully-flat Tor-amplitude reflection is owned by the explicit ring-hom API in
`ScalarExtension.TorAmplitude`.
-/

open CategoryTheory

universe u

/- Lemma 15.67.17: faithfully flat base change reflects Tor-amplitude in `[a, b]`. -/
@[stacks 068S "Lemma 15.67.17"]
#check fun {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (hσ : σ.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hK : DerivedCategory.HasTorAmplitudeIn (R := S)
      ((ModuleCat.derivedExtensionOfScalars σ).obj K) a b) ↦
  (DerivedCategory.HasTorAmplitudeIn.of_faithfullyFlat σ hσ K a b hK :
    DerivedCategory.HasTorAmplitudeIn (R := R) K a b)
