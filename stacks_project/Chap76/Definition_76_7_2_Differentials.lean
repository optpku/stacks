/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f : X.Modules)
