/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} (U : CategoryTheory.Over S)

#check (AlgebraicGeometry.Scheme.PreRelation U : Type (u + 1))
