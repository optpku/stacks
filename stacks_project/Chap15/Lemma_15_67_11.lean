/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Restriction
import StacksCheckRecall

/-!
# Lemma 15.67.11

@stack 066J

Restriction of scalars along a flat ring map preserves a fixed Tor-amplitude interval.  The
shared owner uses the explicit map and its `Flat` proof, which is the reusable form of the
algebra-map specialization in this chapter.
-/

@[expose] public section

open CategoryTheory

universe u

@[stacks 066J "Lemma 15.67.11"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (K : DerivedCategory (ModuleCat B)) (a b : ℤ)
    (hK : DerivedCategory.HasTorAmplitudeIn (R := B) K a b) ↦
  (DerivedCategory.HasTorAmplitudeIn.restrictScalars_of_flat f hf K hK :
    DerivedCategory.HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj K) a b)
