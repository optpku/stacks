/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.AffineRealization
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Cotangent
universe u
/- 92.27.1.1 -/
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.affineScheme :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicGeometry.AlgebraicSpace (Spec Λ)),
    AlgebraicGeometry.AlgebraicSpace.Cotangent.category Λ X ⥤ Scheme.{u})
