module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import ReasLib.Topology.Category.GrpTopCat.Concrete

/-!
# Colimits of topological group objects
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace GrpTopCat

/-- The category of topological group objects has all small colimits. -/
@[stacks 0B21 "topological groups have colimits"]
instance hasColimits : HasColimits (Grp TopCat.{u}) := sorry

/-- Forgetting a topological group object to its ordinary group preserves all small colimits. -/
@[stacks 0B21 "colimits commute with the forgetful functor to groups"]
instance forgetToGrpCat_preservesColimits :
    PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) := sorry

end GrpTopCat
