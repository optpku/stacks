module

public import ReasLib.CategoryTheory.Sites.Descent.Family.DescentDatum
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.3.5

The canonical functor, the identity-family datum, and effectiveness are owned by
`CategoryTheory.DescentDatum`.  No chapter-local singleton overlap instances or alternate
descent-data category are needed.
-/

namespace CategoryTheory

/- The singleton family is the presentation used by the trivial datum. -/
#check @SemiRepresentableFamily.Over.singleton

/- Definition 8.3.5 (1): an object over `U` has a trivial descent datum for the singleton
identity family. -/
@[stacks 026E "(1) trivial descent datum"]
#check @DescentDatum.trivial

#check @DescentDatum.trivial_obj
#check @DescentDatum.trivialObjIso
#check @DescentDatum.trivialOverlapIso
#check @DescentDatum.trivial_iso

/- Definition 8.3.5 (2): pullback along a family gives the canonical descent datum. The
functorial owner includes its action on objects and morphisms. -/
@[stacks 026E "(2) canonical descent datum"]
#check @DescentDatum.canonicalFunctor

#check @DescentDatum.canonicalFunctor_obj_obj
#check @DescentDatum.canonicalFunctor_map_hom

/- Definition 8.3.5 (3): effectiveness means being isomorphic to canonical descent data. -/
@[stacks 026E "(3) effective descent datum"]
#check @DescentDatum.IsEffective

#check @DescentDatum.IsEffective.of_canonical

end CategoryTheory
