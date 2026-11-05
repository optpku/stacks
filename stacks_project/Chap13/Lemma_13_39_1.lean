/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.SmallSet
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.39.1

The reusable statement is the Brown-representability criterion for a detecting
factorization set small in the coproduct universe. Local smallness and smallness
of the functor values on all generator shifts keep the approximation indices in
that universe.
-/

@[stacks 0GYG] #check @CategoryTheory.BrownRepresentability.IsSet

@[stacks 0GYG] #check @CategoryTheory.BrownRepresentability.SmallSet.existsRepresentation

#check @CategoryTheory.BrownRepresentability.SmallSet.isRepresentable
