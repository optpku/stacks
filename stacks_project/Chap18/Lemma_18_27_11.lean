/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 18.27.11

The reusable owner states the filtered-colimit comparison for internal Hom at the level of
finitely presented module sheaves.
-/

@[expose] public section

/- Lemma 18.27.11 (0GMZ): `ihom F` preserves a filtered colimit when `F` is finitely
presented. -/
@[stacks 0GMZ]
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.ihom_isIso
