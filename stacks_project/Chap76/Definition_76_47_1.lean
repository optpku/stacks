module

public import stacks_project.Chap76.Definition_76_47_1_Perfect
import StacksCheckRecall

@[expose] public section

/- Definition 76.47.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is perfect if the equivalent conditions of Lemma 67.22.1 hold with `P` = perfect. -/
@[stacks 06BZ] #check AlgebraicGeometry.AlgebraicSpace.Perfect

/- Definition 76.47.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is perfect at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
perfect restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 06BZ] #check AlgebraicGeometry.AlgebraicSpace.PerfectAt
