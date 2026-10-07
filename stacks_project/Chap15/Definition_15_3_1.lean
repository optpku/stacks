module

import StacksCheckRecall
public import ReasLib.Algebra.Module.StableFree

/-!
# Definition 15.3.1

@stack 0BC3
-/

@[expose] public section

/- Definition 15.3.1 (1): stable isomorphism is owned by the reusable module API. -/
@[stacks 0BC3 "(1), stable isomorphism"] #check @Module.StablyIsomorphic

/- Definition 15.3.1 (2): stable freeness is owned by the reusable module API. -/
@[stacks 0BC3 "(2), stably free module"] #check @Module.StablyFree
