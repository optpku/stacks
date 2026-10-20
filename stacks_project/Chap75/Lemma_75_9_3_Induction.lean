/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Induction

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite.fiber :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U V W : spacesEtaleSite X}
    (j : U ⟶ W) (f : V ⟶ W) [Etale f.left], spacesEtaleSite X)
