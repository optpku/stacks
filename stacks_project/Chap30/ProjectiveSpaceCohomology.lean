/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic

@[expose] public section

namespace AlgebraicGeometry

/- Historical Chapter 30 index: the standard `Proj` model of `ℙⁿ_R` is owned by
`ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic`.  Consumers should use these canonical names
directly rather than a cohomology-specific synonym. -/

#check ProjectiveSpace.grading
#check ProjectiveSpace.scheme

end AlgebraicGeometry
