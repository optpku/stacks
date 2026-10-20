/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import stacks_project.Chap42.Lemma_42_35_3_Vanishing
public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Lemma 42.48.1: proper pushforward of the canonical Gysin-at-infinity cap family along
`i∞ : W∞ ⟶ W` equals proper pushforward of the identity cap family along the lifted zero
section `i₀ : X ⟶ W`, uniformly after every locally finite-type base change of `X`. -/
@[stacks 0F9J] #check
  (AlgebraicGeometry.BivariantClass.gysinAtInfinity_pushforward :
    ∀ {S W : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
      [IsIso (b ∣_ GysinAtInfinity.affinePart X)],
      (GysinAtInfinity.infinityPushforwardCap δ X b :
          CapFamily δ (GysinAtInfinity.toX X b) 0) =
        (GysinAtInfinity.zeroPushforwardCap δ X b :
          CapFamily δ (GysinAtInfinity.toX X b) 0))

end AlgebraicGeometry.BivariantClass
