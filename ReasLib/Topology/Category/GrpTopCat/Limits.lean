module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import ReasLib.Topology.Category.GrpTopCat.Concrete

/-!
# Limits of topological group objects
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace GrpTopCat

/-- The category of topological group objects has all small limits. -/
@[stacks 0B20 "limits of topological groups"]
instance hasLimits : HasLimits (Grp TopCat.{u}) :=
  { has_limits_of_shape := fun J _ ↦ by
      -- Local instance justification (defeq pin): the shape-wise generic group-object limits
      -- instance fixes this size parameter to `u`; the bridge is local to that application.
      let _ : Small.{u} J := inferInstance
      infer_instance }

/-- Forgetting a topological group object to its topological space preserves all small limits. -/
@[stacks 0B20 "limits commute with the forgetful functor to topological spaces"]
instance forgetToTopCat_preservesLimits :
    PreservesLimits (Grp.forget TopCat.{u}) :=
  { preservesLimitsOfShape := fun {J} _ ↦ by
      simpa using (inferInstance : PreservesLimitsOfShape J (Grp.forget TopCat.{u})) }

/-- Forgetting a topological group object to its ordinary group preserves all small limits. -/
@[stacks 0B20 "limits commute with the forgetful functor to groups"]
instance forgetToGrpCat_preservesLimits :
    PreservesLimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) := sorry

end GrpTopCat
