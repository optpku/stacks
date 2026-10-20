/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.HomStack.Basic

open CategoryTheory AlgebraicGeometry

universe u

/- Mapping stacks with scheme domain. -/
#check (AlgebraicGeometry.GroupoidsOver.homStack :
    ∀ {S : Scheme.{u}} (X : Over S) (Z : GroupoidsOver S), GroupoidsOver S)
