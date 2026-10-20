/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.39.1

The reusable statement is the abstract Brown-representability criterion for a
detecting factorization set.  Its prior telescope construction is proof
infrastructure, not part of the chapter-facing API.
-/

@[stacks 0GYG] #check @CategoryTheory.BrownRepresentability.IsSet

@[stacks 0GYG] #check @CategoryTheory.BrownRepresentability.existsRepresentation

#check @CategoryTheory.BrownRepresentability.isRepresentable
