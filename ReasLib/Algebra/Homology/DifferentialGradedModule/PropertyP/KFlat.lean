/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.KFlat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP
public import Mathlib.Tactic.CrossRefAttribute
import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Telescope

/-!
# K-flatness of property P modules

Property P is intrinsic to modules over a differential graded algebra, while K-flatness is a
property of the underlying complex over the ground ring.  This file owns the bridge between
those two abstraction layers.
-/

@[expose] public section

universe u v

namespace DifferentialGradedModule.HasPropertyP

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A property P module over a K-flat DGA is K-flat over the ground ring.  This is the reusable
K-flatness step in Lemma 22.33.8 (0BYZ), independent of any chosen scalar extension. -/
@[stacks 0BYZ "property P modules over a K-flat differential graded algebra are K-flat"]
theorem isKFlat {P : DifferentialGradedModule.{u, v} A} (hA : A.IsKFlat)
    (hP : HasPropertyP A P) : P.IsKFlat := sorry

end DifferentialGradedModule.HasPropertyP
