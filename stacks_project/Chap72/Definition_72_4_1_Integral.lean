/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-! Compatibility facade for the canonical algebraic-space property. -/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsIntegral :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
