/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.ModuleExtension
import StacksCheckRecall

/-!
# Lemma 15.67.14

@stack 066M

If `A → B` is flat, extension of scalars sends an `A`-module of Tor dimension at most `d` to a
`B`-module of Tor dimension at most `d`.  The ReasLib owner is stated for an explicit ring
homomorphism and separately exposes preservation of finite flat resolutions.
-/

@[expose] public section

open CategoryTheory

universe u

@[stacks 066M "Lemma 15.67.14"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (M : ModuleCat A) (d : ℕ)
    (hM : ModuleCat.HasTorDimensionLE (R := A) M d) ↦
  (ModuleCat.HasTorDimensionLE.extendScalars f hf hM :
    ModuleCat.HasTorDimensionLE (R := B) ((ModuleCat.extendScalars f).obj M) d)

@[stacks 066M "finite flat resolution base-change API"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (M : ModuleCat A) (d : ℕ)
    (hM : ModuleCat.HasFiniteFlatResolutionLengthLE M d) ↦
  (ModuleCat.HasFiniteFlatResolutionLengthLE.extendScalars f hf hM :
    ModuleCat.HasFiniteFlatResolutionLengthLE ((ModuleCat.extendScalars f).obj M) d)
