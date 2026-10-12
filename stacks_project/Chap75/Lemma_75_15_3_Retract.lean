/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Retract
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_2_EtaleLocal

/-!
# Retract extensions of perfect complexes from open subspaces

On a quasi-compact quasi-separated algebraic space, a perfect object of `D(𝒪_W)` on a
quasi-compact open subspace is a direct summand of the restriction of a globally perfect
object of `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A perfect object of `D(𝒪_W)` on a quasi-compact open subspace of a quasi-compact
quasi-separated algebraic space is a direct summand of the restriction of a perfect
object of `D(𝒪_X)`. -/
theorem exists_retract_extension_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (W : OpenSubspace X)
    [IsQuasiCompact W.X] (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P) :
    ∃ R : ModuleDerived X,
      ModuleDerived.IsPerfect R ∧
        Nonempty (Retract P ((ModuleDerived.pullback W.ι).obj R)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
