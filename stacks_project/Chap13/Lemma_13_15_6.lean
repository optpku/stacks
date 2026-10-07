module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Resolution
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
# Acyclicity from Monomorphic Resolution Classes

This textbook entry is a direct recall of the reusable resolution-class criterion in ReasLib.
-/

/- Lemma 13.15.6: if every object admits a monomorphism into a member of `P`, and `P` is closed
under the indicated cokernel operation while applying `F` preserves the resulting short exact
sequences, then every member of `P` is bounded-below right acyclic for `F`. -/
@[stacks 05T8]
#check @CategoryTheory.Functor.RightAcyclic.Bounded.of_mem
