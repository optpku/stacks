module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Pretopology.Comparison

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Lemma 7.8.7 (00VX) (1): the family-level tautological replacement
criterion for pretopologies is a thin bridge over the reusable precoverage
comparison API. -/
@[stacks 00VX] #check @Pretopology.isSheaf_of_tautological_covers

/- Lemma 7.8.7 (00VX) (2): mutual tautological replacement gives equivalent
set-valued sheaf conditions. -/
@[stacks 00VX] #check @Pretopology.isSheaf_iff_of_mutual_tautological_covers

/- Lemma 7.8.7 (00VX) (3): refinement first gives an inclusion of generated
topologies through the canonical pretopology Galois insertion. -/
@[stacks 00VX] #check @Pretopology.isSheaf_of_refinement

/- Lemma 7.8.7 (00VX) (4): sheaf transfer along an inclusion of
Grothendieck topologies yields the mutual-refinement comparison. -/
@[stacks 00VX] #check @Pretopology.isSheaf_iff_of_mutual_refinement

end CategoryTheory
