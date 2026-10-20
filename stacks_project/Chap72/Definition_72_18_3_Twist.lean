/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Twist
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_40_4
public import stacks_project.Chap67.Lemma_67_40_5
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap72.Lemma_72_17_3_EulerCharacteristic

/-!
# Compatibility checks for algebraic-space intersection twists

The reusable tensor-twist API is owned by the canonical ReasLib intersection module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check (pullbackTensorPower :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) (j : Fin d), Z.Modules)

#check (pullbackTensorTwist :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ), Z.Modules)

variable {k : Type u} [Field k]
variable {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
variable (i : Z ⟶ X) [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
variable [Abelian X.Modules] [Abelian Z.Modules]
variable [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
variable [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
variable (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
variable (n : Fin d → ℤ)

#check (eulerCharacteristic i L n : ℤ)
#check (eulerCharacteristic_pushforwardStructureTwist_eq i L n :
  AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic
      (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X)
      (pushforwardStructureTwist i L n) = eulerCharacteristic i L n)

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
