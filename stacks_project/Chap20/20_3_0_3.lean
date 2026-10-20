/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Bounded
import StacksCheckRecall

/-!
# Bounded-below derived sections on an open subset

@stack 0717
-/

@[expose] public section

/- 20.3.0.3: bounded-below derived sections on an open subset are the canonical right-derived
functor of module sections evaluation. -/
@[stacks 0717 "bounded-below derived sections on an open subset"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Bounded.functor

end
