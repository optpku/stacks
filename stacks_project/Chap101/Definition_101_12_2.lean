/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_12_2_Submersive
import StacksCheckRecall

@[expose] public section

/- Definition 101.12.2 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
submersive if the continuous map `|X| ⟶ |Y|` is a quotient map. -/
@[stacks 06U6] #check AlgebraicGeometry.AlgebraicStack.Submersive

/- Definition 101.12.2 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
universally submersive if for every morphism of algebraic stacks `Z ⟶ Y` the
base change `Z ×_Y X ⟶ Z` is submersive. -/
@[stacks 06U6] #check AlgebraicGeometry.AlgebraicStack.UniversallySubmersive
