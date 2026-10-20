/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction

/-! Compatibility check for restriction on the small étale site. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
universe u
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : X ⟶ Y) [Etale g]

#check (AlgebraicGeometry.AlgebraicSpace.etaleRestrictionSheaf g (Type (u + 1)) :
  Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
    Sheaf (smallEtaleTopology X) (Type (u + 1)))
