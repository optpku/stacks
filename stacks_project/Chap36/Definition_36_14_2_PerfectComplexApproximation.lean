/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent

universe u

#check (AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes :
  AlgebraicGeometry.Scheme.{u} → Prop)
