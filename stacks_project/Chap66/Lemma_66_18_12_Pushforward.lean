/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-! Compatibility check for coefficient-valued small étale direct image. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
universe u
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward (Type (u + 1)) f :
  Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
    Sheaf (smallEtaleTopology Y) (Type (u + 1)))
