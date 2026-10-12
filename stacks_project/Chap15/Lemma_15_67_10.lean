/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.RestrictionTensor
import StacksCheckRecall

/-!
# Lemma 15.67.10

@stack 0B66

The reusable theorem is stated for an explicit ring homomorphism in
`DerivedCategory.HasTorAmplitudeIn.tensor_restrictScalars`.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

/- Lemma 15.67.10: restricted derived tensor products add Tor-amplitude intervals. -/
@[stacks 0B66 "Lemma 15.67.10"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (K L : DerivedCategory (ModuleCat B)) (a b c d : ℤ)
    (hK : DerivedCategory.HasTorAmplitudeIn (R := B) K a b)
    (hL : DerivedCategory.HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj L) c d) ↦
  (DerivedCategory.HasTorAmplitudeIn.tensor_restrictScalars f K L hK hL :
    DerivedCategory.HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj (K ⊗[B]^L L))
      (a + c) (b + d))
