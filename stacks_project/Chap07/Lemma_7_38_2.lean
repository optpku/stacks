module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Enough

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

/- Lemma 7.38.2 (00YL): a conservative indexed family of points detects monomorphisms,
epimorphisms, equality of sheaf maps, and finite limits and colimits stalkwise.  The five
atomic consequences belong to the reusable `PointFamily` API. -/
@[stacks 00YL] #check @PointFamily.mono_of_stalkwise_injective

@[stacks 00YL] #check @PointFamily.epi_of_stalkwise_surjective

@[stacks 00YL] #check @PointFamily.hom_ext_of_stalkwise

@[stacks 00YL] #check @PointFamily.isLimit_iff_stalkwise

@[stacks 00YL] #check @PointFamily.isColimit_iff_stalkwise

end CategoryTheory.GrothendieckTopology
