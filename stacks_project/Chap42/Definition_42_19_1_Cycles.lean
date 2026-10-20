/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (d : X → ℤ) (k : ℤ)

/- Compatibility check for the shared fixed-dimension cycle-group owner. -/
#check (CycleGroup X d k : Type u)

end AlgebraicGeometry
