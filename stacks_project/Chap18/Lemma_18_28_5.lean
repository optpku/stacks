/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Colimits
import StacksCheckRecall

/-!
# Lemma 18.28.5

Filtered colimits and coproducts preserve flatness for both presheaves and sheaves of modules.
The four statements share one colimit-oriented reusable leaf.
-/

@[expose] public section

/- Lemma 18.28.5 (03EU), presheaves: filtered colimits preserve flatness. -/
@[stacks 03EU "presheaf filtered colimits"]
#check @PresheafOfModules.isFlat_colimit_of_isFiltered

/- Lemma 18.28.5 (03EU), presheaves: coproducts preserve flatness. -/
@[stacks 03EU "presheaf coproducts"]
#check @PresheafOfModules.isFlat_coproduct

/- Lemma 18.28.5 (03EU), sheaves: filtered colimits preserve flatness. -/
@[stacks 03EU "sheaf filtered colimits"]
#check @SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered

/- Lemma 18.28.5 (03EU), sheaves: coproducts preserve flatness. -/
@[stacks 03EU "sheaf coproducts"]
#check @SheafOfModules.RingedSite.isFlat_coproduct
