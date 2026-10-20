/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.RelativeEulerCharacteristic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»

/-! # Relative Euler characteristics of coherent modules over a field -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check (AlgebraicGeometry.AlgebraicSpace.cohomologyFinrank :
    ∀ {k : Type u} [Field k] {S : Scheme.{u}} {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] (i : ℕ), ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.cohomologyFinrank_def :
    ∀ {k : Type u} [Field k] {S : Scheme.{u}} {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] (i : ℕ),
    cohomologyFinrank σ π F i =
      Module.finrank k
        ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj
          ((Modules.toScheme (Over.mk σ)).obj (Modules.higherDirectImage π F i))))

#check (AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic :
    ∀ {k : Type u} [Field k] {S : Scheme.{u}} {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent], ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic_def :
    ∀ {k : Type u} [Field k] {S : Scheme.{u}} {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent],
    eulerCharacteristic σ π F =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) * (cohomologyFinrank σ π F i : ℤ))
