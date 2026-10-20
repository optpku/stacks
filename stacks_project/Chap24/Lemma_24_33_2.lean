/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Closure
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.ModulesOnCategory.QuasiCoherent

/- Lemma 24.33.2 (1): a comparison-defined quasi-coherent subcategory is strictly full. -/
@[stacks 0GZA] #check @isClosedUnderIsomorphisms

/- Lemma 24.33.2 (2): it is stable under retracts. -/
@[stacks 0GZA "saturated"] #check @isStableUnderRetracts

/- Lemma 24.33.2 (3): exact, shift-compatible comparison data makes it triangulated. -/
@[stacks 0GZA "triangulated"] #check @isTriangulated

/- Lemma 24.33.2 (4): preservation by all section and restriction functors makes it closed under
arbitrary direct sums. -/
@[stacks 0GZA "closed under direct sums"] #check @isClosedUnderDirectSums

end CategoryTheory.ModulesOnCategory.QuasiCoherent
