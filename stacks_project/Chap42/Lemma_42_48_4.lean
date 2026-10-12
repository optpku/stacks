/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity.Pushforward
public import stacks_project.Chap42.Lemma_42_48_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.GysinAtInfinity

/- Lemma 42.48.4: capping with the Gysin-at-infinity class after proper pushforward
from `W∞` to `X` recovers the Gysin pullback along `i∞ : W∞ ⟶ W`. -/
@[stacks 0FAR] #check
  (AlgebraicGeometry.BivariantClass.GysinAtInfinity.cap_map_gysin :
    ∀ {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
      [IsIso (b ∣_ affinePart X)] (k : ℤ),
      (capAtBase δ X b k).comp
        ((ChowGroup.map δ (infinityFiber X b) (Over.mk X.hom)
          (infinityToX X b) k).comp (gysinPullback δ X b k)) =
        gysinPullback δ X b k)

end AlgebraicGeometry.BivariantClass.GysinAtInfinity
