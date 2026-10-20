/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AdditiveGroup

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AdditiveGroup.groupScheme :
  (S : Scheme.{u}) → CommGrp (Over S))
