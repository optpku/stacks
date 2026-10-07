module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatRepresentative

/-!
# Flat representatives in a finite Tor-amplitude interval

This file is the source-facing recall for Lemma 15.67.3.

@stack 0654
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.67.3: an object `K` of `D(R)` has Tor-amplitude in `[a, b]` if and only if it is
quasi-isomorphic to a complex of flat `R`-modules supported in `[a, b]`. -/
@[stacks 0654 "Lemma 15.67.3"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (a b : ℤ) ↦
  (Iff.trans (DerivedCategory.hasTorAmplitudeIn_iff_hasFlatRepresentativeIn K a b)
      (DerivedCategory.hasFlatRepresentativeIn_iff K a b) :
    DerivedCategory.HasTorAmplitudeIn R K a b ↔
      ∃ (E : CochainComplex (ModuleCat R) ℤ) (_ : K ≅ DerivedCategory.Q.obj E),
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ HomologicalComplex.IsTermwiseFlat E)

#check @DerivedCategory.HasFlatRepresentativeIn

#check @DerivedCategory.hasFlatRepresentativeIn_iff

#check @DerivedCategory.HasTorAmplitudeIn.hasFlatRepresentativeIn

#check @DerivedCategory.HasFlatRepresentativeIn.hasTorAmplitudeIn
