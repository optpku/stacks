/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_50_4_IntegralClosed

/-!
# Lemma 101.50.4

Let `X` be a decent algebraic stack such that the inertia morphism `I_X ⟶ X`
is quasi-compact. There are canonical bijections between the set of points of
`X`, the set of irreducible closed subsets of `Points X`, and the set of
integral closed substacks of `X`. The bijection from points to irreducible
closed subsets sends `x` to `closure {x}`. The bijection from integral closed
substacks to irreducible closed subsets sends `Z` to `Z.pointsSet`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.50.4 (1): Let `X` be a decent algebraic stack such that the
inertia morphism `I_X ⟶ X` is quasi-compact. There is a canonical bijection
between the set of points of `X` and the set of irreducible closed subsets of
`Points X`, sending `x` to `closure {x}`. -/
@[stacks 0GWE]
theorem pointsEquivIrreducibleCloseds_apply {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    (pointsEquivIrreducibleCloseds X x : Set (Points X)) = closure {x} :=
  sorry

/-- Lemma 101.50.4 (2): Let `X` be a decent algebraic stack such that the
inertia morphism `I_X ⟶ X` is quasi-compact. The reduced induced closed
substack on an irreducible closed subset `T` of `Points X` is an integral
closed substack of `X` whose space of points is `T`. -/
@[stacks 0GWE]
theorem ClosedSubstack.ofIrreducibleClosed_integral_pointsSet {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ClosedSubstack.ofIrreducibleClosed T).Y ∧
      (ClosedSubstack.ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- Lemma 101.50.4 (3): Let `X` be a decent algebraic stack such that the
inertia morphism `I_X ⟶ X` is quasi-compact. The bijection from integral
closed substacks of `X` to irreducible closed subsets of `Points X` sends `Z`
to `Z.pointsSet`, and `Z` determines the same strictly full subcategory as the
reduced induced structure on that set. -/
@[stacks 0GWE]
theorem ClosedSubstack.irreducibleClosed_spec {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (Z : ClosedSubstack X)
    [IsIntegral Z.Y] :
    (Z.irreducibleClosed : Set (Points X)) = Z.pointsSet ∧
      Z.objectProperty =
        (ofIrreducibleClosed Z.irreducibleClosed).objectProperty :=
  sorry

end AlgebraicGeometry.AlgebraicStack
