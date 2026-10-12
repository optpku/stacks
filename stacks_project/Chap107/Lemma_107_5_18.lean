/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Definition_100_12_3_Dimension

/-!
# Dimension along closed immersions of algebraic stacks

A closed immersion of locally Noetherian algebraic stacks cannot increase
dimension at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.18: if `i : Z ⟶ X` is a closed immersion of locally Noetherian
algebraic stacks, and if `z ∈ |Z|` has image `x = Points.map i z` in `|X|`,
then `dimensionAt z ≤ dimensionAt x`. -/
@[stacks 0DRY]
theorem dimensionAt_le_of_closedImmersion {S : Scheme.{u}} {Z X : GroupoidsOver S}
    [AlgebraicStack Z] [AlgebraicStack X] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (i : Z ⟶ X) [ClosedImmersion i] (z : Points Z) :
    dimensionAt z ≤ dimensionAt (Points.map i z) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
