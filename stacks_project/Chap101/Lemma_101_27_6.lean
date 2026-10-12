/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_27_6_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.27.6: if `f ≫ g` is locally of finite presentation and `g` is
locally of finite type, then `f` is locally of finite presentation. -/
@[stacks 06Q6] #check
  (LocallyOfFinitePresentation.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g],
      LocallyOfFinitePresentation f)
