/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude

/-!
# Definition 15.67.1

@stack 0652
-/

@[expose] public section

open CategoryTheory

universe u

/- Definition 15.67.1 (1), tag `0652`: Tor-amplitude in a fixed interval, specialized from the
generic monoidal-derived-category owner to `ModuleCat R`. -/
@[stacks 0652 "(1), Tor-amplitude"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (a b : ℤ) ↦
  (DerivedCategory.HasTorAmplitudeIn R K a b : Prop)

/- Definition 15.67.1 (2), tag `0652`: finite Tor dimension. -/
@[stacks 0652 "(2), finite Tor dimension"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) ↦
  (DerivedCategory.HasFiniteTorDimension R K : Prop)

/- Definition 15.67.1 (3), tag `0652`: Tor dimension at most `d` for a module. -/
@[stacks 0652 "(3), module Tor dimension"]
#check fun {R : Type u} [CommRing R] (M : ModuleCat R) (d : ℕ) ↦
  (ModuleCat.HasTorDimensionLE R M d : Prop)

/- Definition 15.67.1 (4), tag `0652`: finite Tor dimension for a module. -/
@[stacks 0652 "(4), finite module Tor dimension"]
#check fun {R : Type u} [CommRing R] (M : ModuleCat R) ↦
  (ModuleCat.HasFiniteTorDimension R M : Prop)

/- The generic Tor-amplitude owner used by the module-category specialization. -/
#check @DerivedCategory.DerivedTensor.hasTorAmplitudeIn_iff_homology

/- The reusable lower-bound projection from a Tor-amplitude interval. -/
#check @DerivedCategory.DerivedTensor.HasTorAmplitudeIn.hasTorAmplitudeGE
