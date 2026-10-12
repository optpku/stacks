/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.RingedSite.Basic

open CategoryTheory

variable {X Y : RingedSite}
variable (F : X ⥤ Y)

example : RingedSite.Hom Y X := by
  exact { base := F }

example : RingedSite.Hom X Y := by
  exact { base := F }
