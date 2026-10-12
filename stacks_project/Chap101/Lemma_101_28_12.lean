/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian
public import stacks_project.Chap100.Definition_100_4_2_Points

/-!
# Reduced locally Noetherian singleton stacks are gerbes

A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is a gerbe over a reduced, locally Noetherian algebraic space that
likewise has a singleton space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.28.12: Let `Z` be a reduced, locally Noetherian algebraic stack
such that `|Z|` is a singleton. Then `Z` is a gerbe over a reduced, locally
Noetherian algebraic space `A` with `|A|` a singleton. -/
@[stacks 06QK]
theorem exists_gerbeOver_reduced_locallyNoetherian_singleton
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    ∃ (A : AlgebraicSpace S) (π : Z ⟶ A.toGroupoids),
      Gerbe π ∧ IsReduced A.toGroupoids ∧ IsLocallyNoetherian A.toGroupoids ∧
        Nonempty (Points A.toGroupoids) ∧ Subsingleton (Points A.toGroupoids) :=
  sorry

/-- A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is a gerbe. -/
@[stacks 06QK]
instance instIsGerbe_of_isReduced_isLocallyNoetherian_singleton
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    IsGerbe Z :=
  sorry

/-- If a reduced, locally Noetherian algebraic stack with singleton space of
points is a gerbe over an algebraic space, then that algebraic space is
reduced, locally Noetherian, and a singleton on points. -/
theorem isReduced_isLocallyNoetherian_singleton_points_of_gerbeOver
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    {A : AlgebraicSpace S} (π : Z ⟶ A.toGroupoids) [Gerbe π] :
    IsReduced A.toGroupoids ∧ IsLocallyNoetherian A.toGroupoids ∧
      Nonempty (Points A.toGroupoids) ∧ Subsingleton (Points A.toGroupoids) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
