module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_4_8_Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.8 (1): the rule `X' ↦ |X'|` is an inclusion-preserving bijection between
open subspaces of an algebraic space `X` and opens of the topological space `|X|`. -/
@[stacks 03BZ] #check OpenSubspace.exists_of_isOpen
@[stacks 03BZ] #check OpenSubspace.pointsSet_subset_iff

/- Lemma 66.4.8 (2): a family of open subspaces of `X` is a Zariski covering if and only
if `|X| = ⋃ |Xᵢ|`. -/
@[stacks 03BZ] #check isZariskiCover_iff_iUnion_pointsSet

/- Lemma 66.4.8 (3): the small Zariski site `X_Zar` is canonically identified with the
opens site of `|X|` associated to `Opens.grothendieckTopology`. -/
@[stacks 03BZ] #check smallZariskiRangeFunctor_isDenseSubsite
