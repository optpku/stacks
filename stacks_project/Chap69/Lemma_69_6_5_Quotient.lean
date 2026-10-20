/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient.Torsor

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G],
    (G →* Aut W) → (W ⟶ U) → Prop)
