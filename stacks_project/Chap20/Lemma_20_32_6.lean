/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology

/- Lemma 20.32.6 (0D5X): for a morphism of ringed spaces `f : X ⟶ Y` and a derived module `K`,
the presheaf `V ↦ H^i(f⁻¹(V), K)` and the degree-`i` cohomology of `R(f)_* K` have canonically
isomorphic sheafifications. -/
@[stacks 0D5X "cohomology presheaf of a derived pushforward"]
#check @sheafification_isomorphic_pushforwardCohomology

#check @preimagePresheaf
#check @pushforwardPresheaf
#check @preimagePresheaf_isomorphic_pushforward
#check @preimagePresheaf_obj_isomorphic_openHypercohomology
#check @pushforwardPresheaf_obj_isomorphic_openHypercohomology

end
