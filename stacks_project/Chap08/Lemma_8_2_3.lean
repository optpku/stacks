/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Reindex
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf
import StacksCheckRecall

@[expose] public section

/-!
# Hom-presheaf maps of morphisms of fibred categories

The canonical owner is the heterogeneous explicit-cleavage
`CartesianBasedFunctor.HomPresheaf` API.  The fixed-universe `FiberedCategoryOver.Hom` form and
its component formulas remain ergonomic companions.
-/

namespace CategoryTheory

/- Lemma 8.2.3: a morphism of fibred categories over `C` induces the canonical morphism between
the Hom-presheaves of two objects in a fibre. -/
@[stacks 042V]
#check @CartesianBasedFunctor.HomPresheaf.Explicit.map

/- The fixed-universe selected-cleavage specialization. -/
#check @FiberedCategoryOver.Hom.presheafHomMap

/- Its component form. -/
#check @FiberedCategoryOver.Hom.presheafHomMap.app

/- The same component expressed using the selected reindexing equivalences. -/
#check @FiberedCategoryOver.Hom.presheafHomMap.app.apply

end CategoryTheory
