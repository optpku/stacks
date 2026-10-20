/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

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

/-- A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is a gerbe over a reduced, locally Noetherian algebraic space whose
space of points is a singleton. -/
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
