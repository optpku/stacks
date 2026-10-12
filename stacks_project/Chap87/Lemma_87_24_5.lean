/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_24_5_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.24.5: if `g ∘ f` is locally of finite type then so is `f`. -/
@[stacks 0AQ6] #check
  (LocallyOfFiniteType.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType (f ≫ g)],
      LocallyOfFiniteType f)
