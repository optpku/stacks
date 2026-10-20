/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.AtWorstNodal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 53.20.12 (1): the canonical structure-sheaf pushforward map of a proper
connected nodal family is an isomorphism. -/
@[stacks 0GKA] #check
  (AlgebraicGeometry.AtWorstNodal.structureSheafMap_isIso :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [IsProper f] → [AtWorstNodal f] → [GeometricallyConnected f] →
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

/- Lemma 53.20.12 (2): the same canonical map is invertible after every base change. -/
@[stacks 0GKA] #check
  (AlgebraicGeometry.AtWorstNodal.baseChange_structureSheafMap_isIso :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [IsProper f] → [AtWorstNodal f] → [GeometricallyConnected f] →
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap (pullback.snd f g).toShHom))

/- Lemma 53.20.12 (3): the first structure-sheaf higher direct image is finite locally free. -/
@[stacks 0GKA] #check
  (AlgebraicGeometry.AtWorstNodal.higherDirectImageOne_isFiniteLocallyFree :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [IsProper f] → [AtWorstNodal f] → [GeometricallyConnected f] →
      SheafOfModules.IsFiniteLocallyFree
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) 1))

/- Lemma 53.20.12 (4): the canonical first-higher-direct-image comparison is an
isomorphism for every base change, with the coefficient identified with the structure module. -/
@[stacks 0GKA] #check
  (AlgebraicGeometry.AtWorstNodal.higherDirectImageOne_commutesWithBaseChange :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [IsProper f] → [AtWorstNodal f] → [GeometricallyConnected f] →
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (AlgebraicGeometry.AtWorstNodal.higherDirectImageOneBaseChangeMap f g))

/- Lemma 53.20.12 (5): all structure-sheaf higher direct images in degrees at least two vanish. -/
@[stacks 0GKA] #check
  (AlgebraicGeometry.AtWorstNodal.higherDirectImage_isZero_of_two_le :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [IsProper f] → [AtWorstNodal f] → [GeometricallyConnected f] →
      ∀ (q : ℕ), 2 ≤ q → IsZero
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) q))
