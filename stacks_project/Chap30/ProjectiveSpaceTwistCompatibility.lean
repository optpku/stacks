/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import ReasLib.AlgebraicGeometry.ProjectiveSpace.GradedPieces
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map

open AlgebraicGeometry

namespace AlgebraicGeometry

/- Historical Chapter 30 index: standard projective-space data is owned by
`ProjectiveSpace.Basic` and `ProjectiveSpace.GradedPieces`; module-sheaf cohomology and its maps
are owned by `RingedSpace.moduleCohomology` and `RingedSpace.moduleCohomologyMap`. -/

#check ProjectiveSpace.grading
#check ProjectiveSpace.scheme
#check ProjectiveSpace.gradedPiece
#check ProjectiveSpace.topCohomologyDual
#check @RingedSpace.moduleCohomology
#check @RingedSpace.moduleCohomologyMap

end AlgebraicGeometry
