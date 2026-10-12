/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap100.Definition_100_9_1_Immersion

/-!
# Closed points via residual gerbes

On a locally Noetherian algebraic stack, a point is closed if and only if its
residual-gerbe monomorphism is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (ClosedImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Lemma 101.51.4: Let `X` be a locally Noetherian algebraic stack. Let
`x ∈ |X|` with residual gerbe `ι : Z ⟶ X` (Lemma 101.31.3). Then `x` is a
closed point of `|X|` if and only if `ι` is a closed immersion. -/
@[stacks 0H27]
theorem mem_closedPoints_iff_closedImmersion {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian X] {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] :
    x ∈ closedPoints (Points X) ↔ ClosedImmersion ι :=
  sorry

/-- If a residual-gerbe monomorphism is a closed immersion, then the marked
point is a closed point of `|X|`. -/
theorem mem_closedPoints {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] [ClosedImmersion ι] :
    x ∈ closedPoints (Points X) :=
  sorry

/-- On a locally Noetherian algebraic stack, the residual-gerbe monomorphism of
a closed point is a closed immersion. -/
theorem closedImmersion_of_mem_closedPoints {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian X] {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x]
    (hx : x ∈ closedPoints (Points X)) :
    ClosedImmersion ι :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
