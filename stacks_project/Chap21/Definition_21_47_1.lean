/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
import StacksCheckRecall

@[expose] public section

/-!
# Definition 21.47.1

Definition 21.47.1 is represented by `RingedSite.CochainComplex.IsPerfect` and
`RingedSite.Hom.ModuleDerived.IsPerfect` in the shared derived ringed-site API.
-/

/- Definition 21.47.1 (08G5): perfectness is represented by the canonical complex-level and
derived-object predicates below. -/
@[stacks 08G5] #check @RingedSite.CochainComplex.IsPerfect

#check @RingedSite.Hom.ModuleDerived.IsPerfect

end
