/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_23_8_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.23.8: if `f ≫ g` is locally quasi-finite and `g` is quasi-DM, then
`f` is locally quasi-finite. -/
@[stacks 06UG] #check
  (LocallyQuasiFinite.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyQuasiFinite (f ≫ g)] [QuasiDM g],
      LocallyQuasiFinite f)
