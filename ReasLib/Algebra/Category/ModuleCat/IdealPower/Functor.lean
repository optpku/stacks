/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Module.IdealPower.Quotient

/-!
# Functorial ideal-power quotients

This module packages exact-power quotients of modules, their transition maps,
and the canonical projection and transition transformations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w

namespace Ideal.PowerQuotient

variable {R : Type w} [CommRing R]

/-- The identity law for the exact-power quotient map. -/
theorem stageMap_id (I : Ideal R) (n : ℕ) (M : ModuleCat.{w} R) :
    stageMap I (𝟙 M) n = 𝟙 (stage I M n) := sorry

/-- The composition law for the exact-power quotient map. -/
theorem stageMap_comp (I : Ideal R) (n : ℕ)
    {M N P : ModuleCat.{w} R} (f : M ⟶ N) (g : N ⟶ P) :
    stageMap I (f ≫ g) n = stageMap I f n ≫ stageMap I g n := sorry

/-- Quotienting by `I ^ n • ⊤` as an endofunctor of `ModuleCat R`. -/
def stageFunctor (I : Ideal R) (n : ℕ) :
    ModuleCat.{w} R ⥤ ModuleCat.{w} R where
  obj M := stage I M n
  map f := stageMap I f n
  map_id := stageMap_id I n
  map_comp := stageMap_comp I n

/-- The stage functor evaluates to the exact-power quotient stage. -/
theorem stageFunctor_obj (I : Ideal R) (n : ℕ) (M : ModuleCat.{w} R) :
    (stageFunctor I n).obj M = stage I M n := sorry

/-- The stage functor acts on morphisms by `stageMap`. -/
theorem stageFunctor_map (I : Ideal R) (n : ℕ) {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    (stageFunctor I n).map f = stageMap I f n := sorry

/-- The transition map `M / I ^ (n + 1) M ⟶ M / I ^ n M`. -/
def stageStep (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    stage I M (n + 1) ⟶ stage I M n :=
  ModuleCat.ofHom (AdicCompletion.transitionMap I M n.le_succ)

/-- The canonical projection of a module onto its exact-power quotient stage. -/
def stageProjection (I : Ideal R) (n : ℕ) (M : ModuleCat.{w} R) :
    M ⟶ stage I M n :=
  ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule R M)))

/-- Stage projections are natural in the module. -/
theorem stageProjection_naturality (I : Ideal R) (n : ℕ)
    {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    f ≫ stageProjection I n N = stageProjection I n M ≫ stageMap I f n := sorry

/-- Consecutive stage transitions are natural in the module. -/
theorem stageStep_naturality (I : Ideal R) (n : ℕ)
    {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    stageMap I f (n + 1) ≫ stageStep I N n =
      stageStep I M n ≫ stageMap I f n := sorry

/-- The natural transition `stageFunctor I (n + 1) ⟶ stageFunctor I n`. -/
def stageStepNatTrans (I : Ideal R) (n : ℕ) :
    stageFunctor I (n + 1) ⟶ stageFunctor I n where
  app M := stageStep I M n
  naturality _ _ f := stageStep_naturality I n f

end Ideal.PowerQuotient
