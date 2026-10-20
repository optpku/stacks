/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Unramified
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 58.11.1: for the normalization in a finite extension of the function field of a
normal integral scheme, being unramified, étale, and finite étale are equivalent. -/
@[stacks 0BQK]
#check (AlgebraicGeometry.Scheme.FunctionFieldExtension.unramified_tfae :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [IsIntegral X]
    (hX : X.isNormal) (L : Type u) [Field L]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L],
    let ν := (AlgebraicGeometry.Scheme.FunctionFieldExtension.map X L).fromNormalization
    List.TFAE [Unramified ν, Etale ν, IsFinite ν ∧ Etale ν])
