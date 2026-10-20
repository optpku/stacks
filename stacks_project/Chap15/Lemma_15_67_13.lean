/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
import StacksCheckRecall

/-!
# Lemma 15.67.13

@stack 066L

Derived scalar extension preserves a fixed Tor-amplitude interval.  The reusable theorem is
stated for an explicit ring homomorphism and the canonical derived-extension functor.
-/

@[expose] public section

open CategoryTheory

universe u

@[stacks 066L "Lemma 15.67.13"]
#check fun {R S : Type u} [CommRing R] [CommRing S]
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hK : DerivedCategory.HasTorAmplitudeIn (R := R) K a b) (σ : R →+* S) ↦
  (DerivedCategory.HasTorAmplitudeIn.extension hK σ :
    DerivedCategory.HasTorAmplitudeIn (R := S)
      ((ModuleCat.derivedExtensionOfScalars σ).obj K) a b)
