/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology
import StacksCheckRecall

namespace CategoryTheory

/- Lemma 25.5.1 [stacks 01GV]: for an arbitrary hypercovering `K` of `X`, degree-zero Čech
cohomology with coefficients in an abelian sheaf is canonically isomorphic to its sections on
`X`. -/
@[stacks 01GV] #check @Hypercovering.Cech.cohomology_zero_isomorphic_sections

end CategoryTheory
