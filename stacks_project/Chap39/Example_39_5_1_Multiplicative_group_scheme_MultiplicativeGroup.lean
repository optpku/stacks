/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.MultiplicativeGroup.groupScheme :
  CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))))
