/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Specialization.Dimension.Catenary

/-!
# Cohomological Obstruction to Dimension Functions

This optional, sheaf-cohomology-dependent leaf records the obstruction class
for gluing local dimension functions.  It is deliberately not imported by the
lightweight dimension aggregate.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace.CatenarySpace

variable {X : Type u} [TopologicalSpace X]

/-- Remark 5.20.5: a catenary locally Noetherian sober space has a degree-one
constant-sheaf obstruction whose vanishing is equivalent to a global dimension
function. -/
@[stacks 02ID]
theorem exists_dimensionFunction_obstructionClass
    [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] :
    ∃ obstruction :
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
          (AddCommGrpCat.of (ULift ℤ))).H 1,
      obstruction = 0 ↔ ∃ δ : X → ℤ, IsDimensionFunction δ := sorry

end TopologicalSpace.CatenarySpace
