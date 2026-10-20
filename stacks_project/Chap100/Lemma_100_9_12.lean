module

public import stacks_project.Chap100.Lemma_100_9_12_Opens
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

/- Lemma 100.9.12: the rule `U ↦ |U|` is an inclusion-preserving bijection between
open substacks of an algebraic stack `X` and opens of the topological space `|X|`. -/
@[stacks 06FJ] #check OpenSubstack.exists_of_isOpen
@[stacks 06FJ] #check OpenSubstack.pointsSet_subset_iff
