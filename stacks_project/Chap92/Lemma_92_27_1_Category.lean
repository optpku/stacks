/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Category
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Cotangent
universe u
/- 92.27.1.1 -/
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.category :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)), Type (u + 1))
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.forget :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    AlgebraicGeometry.AlgebraicSpace.Cotangent.category Λ X ⥤
      AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)
