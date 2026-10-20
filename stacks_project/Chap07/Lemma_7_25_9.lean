/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.Representable.Relocalization
import StacksCheckRecall

@[expose] public section

/- Lemma 7.25.9 (04IL): representable localization carries relocalization lower shriek to
postcomposition and carries inverse image to pullback along the induced representable map. -/
@[stacks 04IL "(1)"] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.relocalizationInverseImageOverPullback_isIso

@[stacks 04IL "(2)"] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.relocalizationLowerShriekOverMap_isIso
