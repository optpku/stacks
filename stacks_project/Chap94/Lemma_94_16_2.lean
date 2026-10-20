module

public import stacks_project.Chap94.Lemma_94_16_2_Presentation
import StacksCheckRecall

/-!
# Lemma 94.16.2

A surjective smooth 1-morphism from an algebraic space into an algebraic stack
yields a smooth kernel-pair groupoid and an equivalence from the quotient stack.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

/- Lemma 94.16.2 (1): the morphisms s, t of the kernel-pair groupoid (U, R, s, t, c)
are smooth. -/
@[stacks 04T5]
#check groupoid_smooth

/- Lemma 94.16.2 (2): the 1-morphism f_can : [U/R] ⟶ X is an equivalence. -/
@[stacks 04T5]
#check fCan_isEquivalence
