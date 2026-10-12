/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap107.Lemma_107_4_2_ComponentsMap

/-!
# Formal branches surject onto irreducible components through a point

In the situation of Definition 107.4.1, the canonical map from formal branches
of `X` through `x0` onto irreducible components of `|X|` containing `x0` is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.FormalBranches

/-- Lemma 107.4.2: In the situation of Definition 107.4.1 there is a canonical
surjection from the set of formal branches of `X` through `x0` to the set of
irreducible components of `|X|` containing `x0` in `|X|`. -/
@[stacks 0DRB]
theorem toComponent_surjective {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ)
    (hT : Points.mk x0 ∈ (T : Set (Points X))) :
    ∃ b : FormalBranches x0, toComponent x0 hτ b = T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FormalBranches
