module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.Topology.Counterexamples.DiscreteTwoPoint.Sheaf

@[expose] public section

/-!
# Example 7.41.3

The concrete collapse map and its sheaf pushforward are owned by the reusable
discrete-two-point counterexample leaf.
-/

/- The finite-colimit bridge from preservation of initial objects and pushouts
is already canonical mathlib API. -/
#check @CategoryTheory.Limits.preservesFiniteColimits_of_preservesInitial_and_pushouts

#check TopCat.Counterexample.DiscreteTwoPoint.collapse
#check TopCat.Counterexample.DiscreteTwoPoint.pushforward

/- Example 7.41.3 (1) (04D8): the collapse pushforward does not preserve
coequalizers. -/
@[stacks 04D8 "(1)"] #check @TopCat.Counterexample.DiscreteTwoPoint.not_preservesCoequalizers

/- Example 7.41.3 (2) (04D8): the collapse pushforward does not preserve
pushouts. -/
@[stacks 04D8 "(2)"] #check @TopCat.Counterexample.DiscreteTwoPoint.not_preservesPushouts
