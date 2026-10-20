/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Openness

/-! Étale morphisms of algebraic spaces induce open maps on canonical point spaces. -/

universe u

open CategoryTheory AlgebraicGeometry

#check
  (AlgebraicGeometry.AlgebraicSpace.Etale.isOpenMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.Etale f],
      IsOpenMap (AlgebraicSpace.Points.map f))
