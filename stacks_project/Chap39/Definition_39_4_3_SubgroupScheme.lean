/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup

universe u

#check (AlgebraicGeometry.Scheme.ClosedSubgroup :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : CategoryTheory.Over S)
    [CategoryTheory.GrpObj G], Type (u + 1))

#check (AlgebraicGeometry.Scheme.OpenSubgroup :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : CategoryTheory.Over S)
    [CategoryTheory.GrpObj G], Type (u + 1))
