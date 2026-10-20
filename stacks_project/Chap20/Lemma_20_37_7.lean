/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.DerivedCategory.Truncation
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation

/- Lemma 20.37.7 (0D63): if every point has a neighbourhood basis and one local bound above
which `H^p(U, H^q(E))` vanishes for all `q < 0`, then every compatible map from `E` to a derived
limit of its lower truncation tower is an isomorphism. -/
@[stacks 0D63 "locally uniform negative vanishing makes the truncation comparison invertible"]
#check @Comparison.isIso_of_locallyNegative

@[stacks 0D63 "locally negative vanishing condition"]
#check @LocallyNegative
@[stacks 0D63 "shrinking a locally negative neighbourhood"]
#check @LocallyNegative.existsShrink
@[stacks 0D63 "locally negative implies locally eventual"]
#check @LocallyNegative.toLocallyEventual

end
