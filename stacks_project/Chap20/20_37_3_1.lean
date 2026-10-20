/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Sections.Limit

/-
20.37.3.1: the Milnor short exact sequence for open hypercohomology is the canonical reusable
statement `cohomologyShortExact`.
-/

@[stacks 0BKR "20.37.3.1: Milnor short exact sequence for open hypercohomology"]
#check @cohomologyShortExact

end
