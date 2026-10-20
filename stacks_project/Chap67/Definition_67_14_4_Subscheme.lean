module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
import StacksCheckRecall

/-! # Closed subspaces and quasi-coherent ideals

The public ideal owner carries the original actual vanishing subfunctor,
inclusion, intersections/unions, and closed-subspace correspondence.
-/

@[expose] public section

#check @AlgebraicGeometry.AlgebraicSpace.homOfPoint
#check @AlgebraicGeometry.AlgebraicSpace.inclusionPullback
#check @AlgebraicGeometry.AlgebraicSpace.vanishes
#check @AlgebraicGeometry.AlgebraicSpace.subschemeFunctor
@[stacks 03MB] #check @AlgebraicGeometry.AlgebraicSpace.subscheme
#check @AlgebraicGeometry.AlgebraicSpace.subschemeι
#check @AlgebraicGeometry.AlgebraicSpace.subscheme_spec
#check @AlgebraicGeometry.AlgebraicSpace.schemeTheoreticIntersection
#check @AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion
