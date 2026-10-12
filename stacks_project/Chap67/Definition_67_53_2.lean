/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
import StacksCheckRecall

@[expose]
public section

/- Definition 67.53.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is a universal homeomorphism iff for every morphism `Z ⟶ Y` of algebraic
spaces the base change `Z ×_Y X ⟶ Z` induces a homeomorphism
`|Z ×_Y X| ⟶ |Z|`. -/
@[stacks 05Z5] #check AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
