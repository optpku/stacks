module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.13.2: the image of `Spec 𝒪_{X,x} ⟶ X` is the set of
generalizations of `x`. -/
@[stacks 01J7] #check Scheme.range_fromSpecStalk
#check Scheme.mem_range_fromSpecStalk_iff
