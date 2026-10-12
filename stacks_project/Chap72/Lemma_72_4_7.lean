/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

/-!
# Lemma 72.4.7

Let `S` be a scheme. Let `X` be a decent algebraic space over `S`. There are
canonical bijections between the set of points of `X`, the set of irreducible
closed subsets of `Points X`, and the set of integral closed subspaces of `X`.
The bijection from points to irreducible closed subsets sends `x` to
`closure {x}`. The bijection from integral closed subspaces to irreducible
closed subsets sends `Z` to `Z.pointsSet`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.4.7 (1): Let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. There is a canonical bijection between the set of points of `X` and
the set of irreducible closed subsets of `Points X`, sending `x` to
`closure {x}`. -/
@[stacks 0ENF]
theorem pointsEquivIrreducibleCloseds_apply {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) :
    (pointsEquivIrreducibleCloseds X x : Set (Points X)) = closure {x} :=
  sorry

/-- Lemma 72.4.7 (2): Let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. The reduced induced closed subspace on an irreducible closed subset
`T` of `Points X` is an integral closed subspace of `X` whose space of points
is `T`. -/
@[stacks 0ENF]
theorem ClosedSubspace.ofIrreducibleClosed_integral_pointsSet {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ClosedSubspace.ofIrreducibleClosed T).X ∧
      (ClosedSubspace.ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- Lemma 72.4.7 (3): Let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. The bijection from integral closed subspaces of `X` to irreducible
closed subsets of `Points X` sends `Z` to `Z.pointsSet`, and `Z` admits a
unique morphism over `X` to the reduced induced structure on that set. -/
@[stacks 0ENF]
theorem ClosedSubspace.irreducibleClosed_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    (Z.irreducibleClosed : Set (Points X)) = Z.pointsSet ∧
      ∃! f : Z.X ⟶ (ofIrreducibleClosed Z.irreducibleClosed).X,
        f ≫ (ofIrreducibleClosed Z.irreducibleClosed).ι = Z.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
