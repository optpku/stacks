/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AffineEtale

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.AffineEtale.commStructurePresheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u})
