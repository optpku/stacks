/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientPresheaf
public import stacks_project.Chap78.Definition_78_4_1_PreRelation

/-!
# Quotient presheaf of a pre-relation on an algebraic space

This module exposes the quotient presheaf of a pre-relation together with the
canonical pullback instance for algebraic spaces.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientPresheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    {U : CategoryTheory.Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U →
      CategoryTheory.Functor (CategoryTheory.Over S)ᵒᵖ (Type u))
