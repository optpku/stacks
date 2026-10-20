/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap75.Lemma_75_11_2_Pushforward
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap86.«86_3_2_1_Pushforward»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing

/-! # Compatibility interface for relative dualizing complexes -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf placed in degree zero, under its historical spelling. -/
noncomputable abbrev derivedStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleDerived X :=
  structureSheafDerived X

end AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicSpace.Proper f] →
    [AlgebraicGeometry.AlgebraicSpace.Flat f] →
    [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f] → Type (u + 1))
