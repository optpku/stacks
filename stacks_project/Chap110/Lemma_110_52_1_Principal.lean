/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Principal.Category

/-! # Principal homogeneous spaces under a group algebraic space -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupAlgebraicSpace.Principal.forget :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
    GroupAlgebraicSpace.Principal.Obj G ⥤ Over S)

#check (AlgebraicGeometry.GroupAlgebraicSpace.Principal.stack :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
    StackOver.Groupoids (Scheme.fppfTopology.over S))
