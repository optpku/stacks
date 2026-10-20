/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Truncation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.7

The reusable owner is the generic truncation-comparison criterion with the canonical basiswise
eventual predicate.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.7 (0D6M): a compatible lower-truncation comparison is an isomorphism under
basiswise eventual cohomology-sheaf vanishing. -/
@[stacks 0D6M]
#check @Comparison.isIso_of_eventual

#check @Basis.eventual
#check @Basis.eventual.of_uniform
