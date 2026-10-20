/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Moduli
import StacksCheckRecall

/-!
# Uniform categorical moduli spaces of well-nigh affine stacks

A well-nigh affine algebraic stack admits a uniform categorical moduli space in
the category of affine schemes. That morphism is separated, quasi-compact, and
a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 106.13.4. Let the algebraic stack `X` be well-nigh affine. There
exists a uniform categorical moduli space `f : X ⟶ M.toGroupoids` in the
category of affine schemes. The morphism is separated, quasi-compact, and a
universal homeomorphism. -/
@[stacks 0DUP] #check
  (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.exists_isUniformCategoricalModuliSpaceIn_isAffine :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [IsWellNighAffine X],
    ∃ (M : AlgebraicSpace S) (f : X ⟶ M.toGroupoids),
      IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f)

#check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.instSeparated :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f],
    Separated f)

#check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.instQuasiCompact :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f],
    QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.instUniversalHomeomorphism :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f],
    UniversalHomeomorphism f)
