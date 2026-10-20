/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteModels

universe u

/- Lemma 75.30.1: the affine étale presentation of derived quasi-coherent modules. -/
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.AffineEtale :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 2))
