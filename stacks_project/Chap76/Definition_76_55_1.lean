module

public import stacks_project.Chap76.Definition_76_55_1_AtWorstNodal
import StacksCheckRecall

@[expose] public section

/- Definition 76.55.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is at-worst-nodal of relative dimension 1 if the equivalent conditions of Lemma 67.22.1
hold with `P` = at-worst-nodal of relative dimension 1. -/
@[stacks 0DSE] #check AlgebraicGeometry.AlgebraicSpace.AtWorstNodal
