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
# Lemma 21.23.9

The reusable owner is the uniform-basis truncation-comparison criterion in ReasLib.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.9 (08U3): a uniform basiswise eventual-vanishing bound makes a compatible
lower-truncation comparison an isomorphism. -/
@[stacks 08U3]
#check @Comparison.isIso_of_uniform

#check @Basis.eventual.of_uniform
