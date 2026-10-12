/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import stacks_project.Chap100.Lemma_100_9_12_Opens
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_5_1

/-!
# Dense open gerbe in a reduced algebraic stack

A reduced algebraic stack whose inertia morphism is quasi-compact admits a
dense open substack which is a gerbe over some algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Proposition 101.29.1: Let `X` be a reduced algebraic stack such that the
inertia morphism `I_X ⟶ X` is quasi-compact. Then there exists a dense open
substack `U ⊂ X` which is a gerbe. -/
@[stacks 06RC]
theorem exists_dense_open_isGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsReduced X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    ∃ U : OpenSubstack X, IsGerbe U.Y ∧ Dense U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack
