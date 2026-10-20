/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Projective.LocalRing
import StacksCheckRecall

/-!
# Projective modules over local rings

@stack 0593

The arbitrary-projective local freeness theorem is canonically owned by
`Module.Projective.free_of_isLocalRing`.
-/

@[expose] public section

/- Theorem 10.85.4 (Tag 0593): every projective module over a local ring is free. -/
@[stacks 0593]
#check @Module.Projective.free_of_isLocalRing
