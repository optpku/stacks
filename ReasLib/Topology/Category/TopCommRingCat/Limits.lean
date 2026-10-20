module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Limits of topological commutative rings
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCommRingCat

/-- The category of topological commutative rings has all small limits. -/
@[stacks 0B23 "existence of limits in topological commutative rings"]
instance hasLimits : HasLimits TopCommRingCat.{u} := sorry

/-- Forgetting a topological commutative ring to its topological space preserves all small limits. -/
@[stacks 0B23 "limits are preserved by the forgetful functor to topological spaces"]
instance forgetToTopCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) := sorry

/-- Forgetting a topological commutative ring to its commutative ring preserves all small limits. -/
@[stacks 0B23 "limits are preserved by the forgetful functor to commutative rings"]
instance forgetToCommRingCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := sorry

end TopCommRingCat
