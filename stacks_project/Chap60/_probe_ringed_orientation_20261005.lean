module

import ReasLib.AlgebraicGeometry.RingedSite.Basic

open CategoryTheory

variable {X Y : RingedSite}
variable (F : X ⥤ Y)

example : RingedSite.Hom Y X := by
  exact { base := F }

example : RingedSite.Hom X Y := by
  exact { base := F }
