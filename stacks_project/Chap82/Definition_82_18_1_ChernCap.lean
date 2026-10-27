/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ClosureIntegral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.GenericSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-! # The original EQK/EQQ target with the concrete closed-image pullback

This is the source-facing ChernCap component, with the same good-space
parameters and the exact point-closure target. Its line module and section
use the explicit geometric/tensor pullback and the concrete generic
restriction. No new affine, decency, or quasi-separated hypothesis is added.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom



variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (L : X.Modules.{u}) [isInvertibleObject L]

#check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_apply :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (L : X.Modules) [isInvertibleObject L]
    (k : ℤ) (α : cycleGroup f δ (k + 1)),
    firstChernClassCap f δ L k α =
      chowMk f δ k ⟨firstChernCycle f δ L k α, firstChernCycle_mem f δ L k α⟩)

end AlgebraicGeometry.AlgebraicSpace.Hom
