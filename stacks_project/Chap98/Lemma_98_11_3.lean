/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 98.11.3: let `S` be a scheme and let `X` be an algebraic stack over
`S`. The following are equivalent: `X` is a stack in setoids and
`X ⟶ (Sch/S)_fppf` is limit preserving on objects; `X` is a stack in setoids
and limit preserving; `X` is representable by an algebraic space locally of
finite presentation over `S`. -/
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
            AlgebraicSpace.LocallyOfFinitePresentation (AlgebraicSpace.toBase F)] :=
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
  sorry

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
          AlgebraicSpace.LocallyOfFinitePresentation (AlgebraicSpace.toBase F) :=
  sorry

/-- An algebraic stack is a stack in setoids and limit preserving if and only if
it is representable by an algebraic space locally of finite presentation over
`S`. -/
theorem inSetoids_limitPreserving_iff_algebraicSpace {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
        Groupoids.LimitPreserving X) ↔
      ∃ F : AlgebraicSpace S,
        Nonempty (X ≌ F.toGroupoids) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (AlgebraicSpace.toBase F) :=
  sorry

/-- Representability by an algebraic space locally of finite presentation over
`S` implies representability by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_of_locallyOfFinitePresentation
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (h : ∃ F : AlgebraicSpace S,
      Nonempty (X ≌ F.toGroupoids) ∧
        AlgebraicSpace.LocallyOfFinitePresentation (AlgebraicSpace.toBase F)) :
    IsRepresentableByAlgebraicSpace X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
