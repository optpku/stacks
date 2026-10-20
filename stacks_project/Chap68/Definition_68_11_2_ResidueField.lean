/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Residue fields of decent algebraic spaces

The residue-field construction and its canonical morphism are provided by
`ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField`.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.residueField :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), CommRingCat.{u})
