/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
open scoped AlgebraicGeometry.RingedSpaceCohomology

/- Lemma 20.32.3 (0BKJ): the sheaf associated to the objectwise cohomology presheaf
`𝓗'[q](X, K)` is canonically isomorphic to the degree-`q` cohomology sheaf `𝓗[q](X, K)`. -/
@[stacks 0BKJ "sheafification of objectwise cohomology"]
#check @sheafification_isomorphic

@[stacks 0BKJ "objectwise cohomology presheaf"]
#check @presheaf
@[stacks 0BKJ "objectwise cohomology sheaf"]
#check @sheaf
@[stacks 0BKJ "objectwise cohomology presheaf on an open"]
#check @presheaf_obj_isomorphic_openHypercohomology

end
