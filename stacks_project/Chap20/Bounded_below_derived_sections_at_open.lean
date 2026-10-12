/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Bounded
import StacksCheckRecall

/-!
# Bounded-below derived sections on open subsets

@stack 0717
-/

@[expose] public section

open AlgebraicGeometry

/- 20.3.0.3: bounded-below derived sections are the canonical right-derived functor of module
sections on an open subset. -/
@[stacks 0717 "bounded-below derived sections on an open subset"]
#check @RingedSpace.Module.Derived.Sections.Bounded.functor
#check @RingedSpace.Module.Derived.Sections.Bounded.unit

end
