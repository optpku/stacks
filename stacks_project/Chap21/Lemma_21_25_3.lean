/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Limit.BoundedBasis
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.25.3 (0D6T) is the bounded-cohomology-basis criterion for degreewise eventual values of a
bounded-below tower.  The reusable statement is owned by
`DerivedCategory.Plus.CohomologyIn.homology_isomorphic_of_boundedBasis`.
-/

open CategoryTheory

@[stacks 0D6T]
#check @DerivedCategory.Plus.CohomologyIn.homology_isomorphic_of_boundedBasis

#check @DerivedCategory.Plus.CohomologyIn.homology_isomorphic_at_of_boundedBasis
#check @DerivedCategory.Plus.CohomologyIn.homologyTower
#check @SequentialInverseSystem.IsEventuallyConstantWithValue

end
