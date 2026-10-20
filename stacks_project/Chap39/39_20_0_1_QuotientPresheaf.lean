/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf

universe u

#check (@AlgebraicGeometry.Scheme.PreRelation.quotientPresheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U : CategoryTheory.Over S},
    AlgebraicGeometry.Scheme.PreRelation U →
      CategoryTheory.Functor (CategoryTheory.Over S)ᵒᵖ (Type u))
