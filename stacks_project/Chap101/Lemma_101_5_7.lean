module

public import stacks_project.Chap101.Lemma_101_5_7_Square
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Presentation square of the inertia stack

For an algebraic stack `X` with presentation `[U/R] ⟶ X`, the stabilizer
group algebraic space `G/U` of `(U, R, s, t, c)` fits in a 2-fibre product
square `G ⟶ U` over `I_X ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- Lemma 101.5.7: Let `X` be an algebraic stack. Let `[U/R] ⟶ X` be a
presentation. Let `G / U` be the stabilizer group algebraic space associated to
the groupoid `(U, R, s, t, c)`. Then the square with vertices `G`, `U`, `I_X`,
and `X` is a fibre product of algebraic stacks. -/
@[stacks 06PR, instance]
instance presentationInertiaCone_isBilimit {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X) :
    (presentationInertiaCone P).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
