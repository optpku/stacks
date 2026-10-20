/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.TopCohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 21.43.3 (0GZQ): for a canonically quasi-coherent derived module `K`, if
`(DerivedCategory.homologyFunctor _ i).obj K` is zero for every `i > b`, then its degree-`b`
cohomology is quasi-coherent. -/
@[stacks 0GZQ]
#check @CategoryTheory.ModulesOnCategory.topCohomology_isQuasicoherent

/- The reusable core expresses the same bounded-above hypothesis using the canonical
`DerivedCategory.IsLE` predicate. -/
#check @CategoryTheory.ModulesOnCategory.topCohomology_isQuasicoherent_of_isLE
