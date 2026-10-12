/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- Properness over a base for a legacy algebraic-space closed subset. -/
abbrev IsProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) : Prop :=
  Proper ((ClosedSubspaceStructure.reduced T).ι ≫ f)

/- A legacy typed view of the properness predicate. -/
#check (IsProperOver : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  (T : Closeds (Points X)), Prop)

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
