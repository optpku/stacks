/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Sections.Limit

/-
Remark 20.37.3: for a sequential inverse system `(K_n)` with derived limit `K`, open
hypercohomology satisfies the Milnor short exact sequence.  This is the source-facing reading of
the canonical reusable theorem `cohomologyShortExact`.
-/

@[stacks 0D60 "Remark 20.37.3: Milnor short exact sequence for open hypercohomology"]
#check @cohomologyShortExact

end
