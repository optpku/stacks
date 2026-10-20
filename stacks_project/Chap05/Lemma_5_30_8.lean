/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCommRingCat.Limits
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

/- Lemma 5.30.8: the canonical owner is `TopCommRingCat`, since the Stacks Project convention
uses commutative rings. -/
@[stacks 0B23 "existence of limits in topological commutative rings"]
#check (inferInstance : HasLimits TopCommRingCat.{u})

@[stacks 0B23 "limits are preserved by the forgetful functor to topological spaces"]
#check (inferInstance : PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}))

@[stacks 0B23 "limits are preserved by the forgetful functor to commutative rings"]
#check (inferInstance : PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}))
