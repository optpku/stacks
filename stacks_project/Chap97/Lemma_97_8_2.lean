/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Definition_97_8_1_Algebraic

/-!
# Algebraic morphisms to algebraic stacks

If a 1-morphism of stacks in groupoids over `(Sch/S)_fppf` is algebraic and
the target is an algebraic stack, then the source is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 97.8.2: Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `Y` is an algebraic stack, and `F`
is algebraic, then `X` is an algebraic stack. -/
@[stacks 05XY]
theorem of_algebraic {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [AlgebraicStack Y] (F : X ⟶ Y) [Groupoids.Hom.Algebraic F] :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
