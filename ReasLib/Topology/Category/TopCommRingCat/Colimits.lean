/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Colimits of topological commutative rings
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCommRingCat

/-- The category of topological commutative rings has all small colimits. -/
@[stacks 0B24 "topological commutative rings have colimits"]
instance hasColimits : HasColimits TopCommRingCat.{u} := sorry

/-- Forgetting a topological commutative ring to its commutative ring preserves all small
colimits. -/
@[stacks 0B24 "colimits are preserved by the forgetful functor to commutative rings"]
instance forgetToCommRingCat_preservesColimits :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := sorry

end TopCommRingCat
