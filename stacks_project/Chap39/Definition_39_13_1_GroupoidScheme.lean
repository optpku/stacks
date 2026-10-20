/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

universe u

#check (AlgebraicGeometry.GroupoidScheme :
  (S : AlgebraicGeometry.Scheme.{u}) → Type (u + 1))

#check (AlgebraicGeometry.GroupoidScheme.Hom :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.GroupoidScheme S → AlgebraicGeometry.GroupoidScheme S → Type u)
