/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime
public import stacks_project.Chap68.Lemma_68_20_2
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
