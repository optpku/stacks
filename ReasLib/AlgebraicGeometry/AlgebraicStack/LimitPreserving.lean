/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Algebraic stacks in setoids that are limit preserving

For an algebraic stack `X` over a scheme `S`, being a stack in setoids that is
limit preserving (equivalently, whose structure morphism to `(Sch/S)_fppf` is
limit preserving on objects) is equivalent to being representable by an
algebraic space locally of finite presentation over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For an algebraic stack `X` over a scheme `S`, the following are equivalent:
`X` is a stack in setoids and `X ⟶ (Sch/S)_fppf` is limit preserving on objects;
`X` is a stack in setoids and limit preserving; `X` is representable by an
algebraic space locally of finite presentation over `S`. -/
@[stacks 07XN]
theorem inSetoids_limitPreserving_tfae {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    List.TFAE
      [IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
          Groupoids.Hom.LimitPreservingOnObjects
            (baseProjection.{u + 1, u, u + 1} X),
        IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
          Groupoids.LimitPreserving X,
        ∃ F : AlgebraicSpace S,
          Nonempty (X ≌ F.toGroupoids) ∧
            AlgebraicSpace.LocallyOfFinitePresentation
              (AlgebraicSpace.SchemeRealization.toBase F)] :=
  sorry

/-- An algebraic stack is a stack in setoids whose structure morphism is limit
preserving on objects if and only if it is a stack in setoids and limit
preserving. -/
theorem inSetoids_limitPreservingOnObjects_iff_limitPreserving
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
        Groupoids.Hom.LimitPreservingOnObjects
          (baseProjection.{u + 1, u, u + 1} X)) ↔
      (IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
        Groupoids.LimitPreserving X) :=
  (inSetoids_limitPreserving_tfae X).out 0 1

/-- An algebraic stack is a stack in setoids whose structure morphism is limit
preserving on objects if and only if it is representable by an algebraic space
locally of finite presentation over `S`. -/
theorem inSetoids_limitPreservingOnObjects_iff_algebraicSpace
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
        Groupoids.Hom.LimitPreservingOnObjects
          (baseProjection.{u + 1, u, u + 1} X)) ↔
      ∃ F : AlgebraicSpace S,
        Nonempty (X ≌ F.toGroupoids) ∧
          AlgebraicSpace.LocallyOfFinitePresentation
            (AlgebraicSpace.SchemeRealization.toBase F) :=
  (inSetoids_limitPreserving_tfae X).out 0 2

/-- An algebraic stack is a stack in setoids and limit preserving if and only if
it is representable by an algebraic space locally of finite presentation over
`S`. -/
theorem inSetoids_limitPreserving_iff_algebraicSpace {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
        Groupoids.LimitPreserving X) ↔
      ∃ F : AlgebraicSpace S,
        Nonempty (X ≌ F.toGroupoids) ∧
          AlgebraicSpace.LocallyOfFinitePresentation
            (AlgebraicSpace.SchemeRealization.toBase F) :=
  (inSetoids_limitPreserving_tfae X).out 1 2

end AlgebraicGeometry.AlgebraicStack
