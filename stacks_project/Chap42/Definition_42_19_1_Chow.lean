/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

/- Compatibility check for the shared Chow-group owner. -/
#check (ChowGroup X d k : Type u)

end AlgebraicGeometry
