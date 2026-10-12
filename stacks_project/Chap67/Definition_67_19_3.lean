/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
import StacksCheckRecall

@[expose] public section

/- Definition 67.19.3: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally injective if for every morphism `Y' ⟶ Y` of algebraic spaces
over `S` the induced map `|Y' ×_Y X| ⟶ |Y'|` is injective. -/
@[stacks 03MV] #check AlgebraicGeometry.AlgebraicSpace.UniversallyInjective

#check AlgebraicGeometry.AlgebraicSpace.universallyInjective_iff
#check AlgebraicGeometry.AlgebraicSpace.universallyInjective_iff_injective_of_isPullback
