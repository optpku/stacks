/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a quasi-compact and quasi-separated algebraic space, the inclusion of derived
modules with quasi-coherent cohomology into all derived modules admits a right
adjoint. -/
instance inclusionIsLeftAdjoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    (inclusion X).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
