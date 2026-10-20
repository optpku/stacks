/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.RingedTopos

@[expose] public section

universe w l

/- This compatibility bridge re-exports the lifted structure-sheaf and ringed-topos APIs. -/
#check (AlgebraicGeometry.Scheme.Site.ringUniverseLiftObj.{w, l} :
  RingCat.{w} → RingCat.{max w l})
