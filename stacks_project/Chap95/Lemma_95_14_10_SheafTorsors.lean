/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.SheafCategory

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors.baseChangeGroupSheaf :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    {U : Over S} (b : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ B),
    Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u})
