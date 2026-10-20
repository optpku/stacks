/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Hom
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject

/-! # Local morphisms of complete local algebras over a scheme -/

@[expose] public section

universe u

variable {S : AlgebraicGeometry.Scheme.{u}}

#check (AlgebraicGeometry.CompleteLocalSAlgebra.Hom :
  AlgebraicGeometry.CompleteLocalSAlgebra S → AlgebraicGeometry.CompleteLocalSAlgebra S → Type u)
