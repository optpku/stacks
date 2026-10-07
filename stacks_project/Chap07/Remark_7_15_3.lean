module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Types
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open CategoryTheory.Types

universe u

namespace CategoryTheory.ObjectProperty

/- Remark 7.15.3 (00XD) is a direct recall of the canonical induced-topology
and cover-dense comparison.  The former Chapter-local construction of an
endomorphism-image quasi-inverse was proof infrastructure; the stable
library-facing owner is `Functor.sheafInducedTopologyEquivOfIsCoverDense`. -/
@[stacks 00XD] #check @Functor.sheafInducedTopologyEquivOfIsCoverDense
#check @Functor.inducedTopology
#check @typesGrothendieckTopology
#check @typeEquiv

end CategoryTheory.ObjectProperty
