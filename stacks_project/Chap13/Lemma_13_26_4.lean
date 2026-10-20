/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.FiniteInjective.Factor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.4

Extension across strict monomorphisms is the reusable filtered analogue of
`Injective.factors`, so the theorem is owned by ReasLib rather than by this chapter facade.
-/

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

/- Lemma 13.26.4 (`05TR`): a morphism to a finite filtered-injective object extends across a
strict monomorphism. -/
@[stacks 05TR] #check @factors

end CategoryTheory.FilteredObject.Finite.FilteredInjective
