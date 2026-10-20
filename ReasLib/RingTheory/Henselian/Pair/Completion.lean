/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.AdicCompletion.Congruence
public import ReasLib.RingTheory.Henselian.Pair.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pair Henselization and adic completion

This file owns the canonical comparison maps between a Noetherian ring pair, its Henselization,
and its adic completion.

@stack 0AGV
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace RingPairCat

variable (X : RingPairCat.{u}) [IsNoetherianRing X.ring]
variable [henselianPairInclusion.IsRightAdjoint]

/-- The extension of the distinguished ideal of `X` to its adic completion. -/
@[stacks 0AGV "extended ideal in the adic completion"]
abbrev adicCompletionIdeal : Ideal (AdicCompletion X.ideal X.ring) :=
  Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal

/-- The ring pair formed by the adic completion and the extended distinguished ideal. -/
@[stacks 0AGV "adic-completion ring pair"]
abbrev adicCompletionPair : RingPairCat.{u} :=
  pairOfIdeal (adicCompletionIdeal X)

/-- The adic-completion pair of a Noetherian pair is Henselian. -/
theorem adicCompletion_henselian :
    HenselianRing (AdicCompletion X.ideal X.ring) (adicCompletionIdeal X) := sorry

/-- The quotient square defining the morphism from a pair to its adic-completion pair commutes. -/
theorem toAdicCompletionPair_commutes :
    CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (adicCompletionIdeal X)) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom
          (Ideal.quotientMap (adicCompletionIdeal X)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map) := sorry

/-- The canonical morphism from a Noetherian ring pair to its adic-completion pair. -/
@[stacks 0AGV "map to the adic-completion pair"]
def toAdicCompletionPair : X ⟶ adicCompletionPair X :=
  InducedCategory.homMk <|
    Arrow.homMk
      (CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)))
      (CommRingCat.ofHom
        (Ideal.quotientMap (adicCompletionIdeal X)
          (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map))
      (toAdicCompletionPair_commutes X)

/-- The canonical ring map `A^h → A^∧` induced by the universal property of pair
Henselization. -/
@[stacks 0AGV "map from pair Henselization to adic completion"]
def henselizationToAdicCompletion :
    henselizationRing X →+* AdicCompletion X.ideal X.ring :=
  let comparison :=
    ((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
      ⟨adicCompletionPair X, adicCompletion_henselian X⟩).symm
      (toAdicCompletionPair X)
  ringHom comparison.hom

/-- The map from the `I`-adic completion of `A` to the `I`-adic completion of the underlying
`A`-module of `A^h`. -/
@[stacks 0AGV "completion map to the Henselization"]
abbrev adicCompletionMapToHenselization :
    AdicCompletion X.ideal X.ring →ₗ[AdicCompletion X.ideal X.ring]
      AdicCompletion X.ideal (henselizationRing X) :=
  AdicCompletion.map X.ideal (Algebra.linearMap X.ring (henselizationRing X))

/-- Lemma 15.12.4 (1): Henselization does not change the `I`-adic completion. -/
@[stacks 0AGV "Lemma 15.12.4 (1)"]
theorem adicCompletion_map_toHenselization_bijective :
    Function.Bijective (adicCompletionMapToHenselization X) := sorry

/-- Lemma 15.12.4 (2): the Henselization ring of a Noetherian pair is Noetherian. -/
@[stacks 0AGV "Lemma 15.12.4 (2)"]
theorem henselizationRing_isNoetherian :
    IsNoetherianRing (henselizationRing X) := sorry

/-- Lemma 15.12.4 (4): the canonical map `A^h → A^∧` is flat. -/
@[stacks 0AGV "Lemma 15.12.4 (4)"]
theorem henselizationToAdicCompletion_flat :
    RingHom.Flat (henselizationToAdicCompletion X) := sorry

/-- Lemma 15.12.4 (5): the canonical map `A^h → A^∧` is faithfully flat. -/
@[stacks 0AGV "Lemma 15.12.4 (5)"]
theorem henselizationToAdicCompletion_faithfullyFlat :
    RingHom.FaithfullyFlat (henselizationToAdicCompletion X) := sorry

end RingPairCat
