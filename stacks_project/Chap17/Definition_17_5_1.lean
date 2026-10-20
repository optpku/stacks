/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}} (M : X.Modules)

/- Definition 17.5.1 (1): the support of an `𝒪_X`-module is the set of points where its stalk is
nonzero. -/
@[stacks 01AT "module support"]
#check RingedSpace.moduleSupport M

/- Membership in the support of a module sheaf can be expressed by a nonzero stalk element. -/
#check RingedSpace.mem_moduleSupport_iff M

variable (s : M.sections)

/- Definition 17.5.1 (2): the support of a global section is the set of points where its germ is
nonzero. -/
@[stacks 01AT "global section support"]
#check SheafOfModules.sectionSupport s

/- Membership in the support of a global section is nonvanishing of its germ. -/
#check SheafOfModules.mem_sectionSupport_iff s

end AlgebraicGeometry
