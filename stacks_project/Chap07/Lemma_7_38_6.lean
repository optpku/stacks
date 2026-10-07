module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Exactness

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology

namespace CategoryTheory

/- Lemma 7.38.6 (0F4G): if `u : C ⥤ D` is continuous, `P` is a conservative family of points
of `(D, K)`, and every composite `u ⋙ Φ.fiber` is naturally isomorphic to the fiber functor of a
point of `(C, J)`, then the induced inverse image on set-valued sheaves is left exact.  The
formal conclusion is a morphism of topoi; this does not incorrectly strengthen the hypothesis to
the project-specific `IsMorphismOfSites`, whose additional `RepresentablyFlat` field is not part
of the source assumption. -/
@[stacks 0F4G] #check @Functor.HasPointwiseFiberRealization.morphismOfTopoiIn

end CategoryTheory
