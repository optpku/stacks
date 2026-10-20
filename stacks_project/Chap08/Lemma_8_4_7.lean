/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Hom
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/-
Lemma 8.4.7 (04WQ): a morphism of fibred categories is fully faithful exactly
when all its canonical fiberwise Hom-presheaf maps are isomorphisms.  For
stacks these Hom-presheaves are sheaves, giving the source formulation.
-/
@[stacks 04WQ "full faithfulness via Hom-sheaves"]
#check @StackOver.Hom.SheafMap.fullyFaithful_iff_isIso
#check @StackOver.Hom.sheafHomMap

/- With independent total-category universes, the same criterion is owned directly by the
common-universe cartesian Hom-presheaf map. -/
#check @CartesianBasedFunctor.HomPresheaf.Explicit.map.fullyFaithful_iff_isIso
#check @CartesianBasedFunctor.HomPresheaf.Chosen.map.fullyFaithful_iff_isIso

#check @StackOver.Hom.PresheafMap.fullyFaithful_iff_isIso
#check @FiberedCategoryOver.Hom.SheafMap.fullyFaithful_iff_isIso
#check @FiberedCategoryOver.Hom.presheafHomMap.fullyFaithful_iff_isIso

end CategoryTheory
