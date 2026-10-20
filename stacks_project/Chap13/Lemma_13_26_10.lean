/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.InjectiveHomotopy
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.10

The cochain-level null-homotopy statement is the bridge view of the normalized finite
filtered-injective orthogonality API in
`ReasLib.CategoryTheory.Filtration.Derived.{Preadditive,InjectiveHomotopy}`.
-/

namespace CategoryTheory.FilteredObject.FiniteDerived.FilteredInjective

/- Lemma 13.26.10 (`05TX`): every morphism from a filtered acyclic complex to a bounded-below
complex of filtered injectives is homotopic to zero. -/
@[stacks 05TX] #check @nullHomotopy

end CategoryTheory.FilteredObject.FiniteDerived.FilteredInjective
