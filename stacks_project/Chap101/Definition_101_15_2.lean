/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

/- Definition 101.15.2: a morphism `f : X ⟶ Y` of algebraic stacks is a
universal homeomorphism if for every morphism of algebraic stacks `Z ⟶ Y` the
map of topological spaces `|Z ×_Y X| ⟶ |Z|` is a homeomorphism. -/
@[stacks 0CI7] #check AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
