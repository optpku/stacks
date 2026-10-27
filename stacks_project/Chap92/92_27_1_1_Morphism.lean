/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Ringed
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Cotangent
universe u
/- 92.27.1.1 -/
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.structureSheaf :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    Sheaf (AlgebraicGeometry.AlgebraicSpace.Cotangent.topology Λ X) CommRingCat.{u + 1})
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.π :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    RingedSite.ToposHom
      (AlgebraicGeometry.AlgebraicSpace.Cotangent.underlineRingedSite Λ X)
      (AlgebraicGeometry.AlgebraicSpace.commRingedSiteLift X))
