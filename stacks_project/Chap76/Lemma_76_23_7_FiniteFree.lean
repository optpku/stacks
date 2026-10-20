/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteFree

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Finite freeness in an étale neighbourhood of a point of an algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.finiteFreeEtaleAt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)
