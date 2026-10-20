/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Localization
import StacksCheckRecall

/-!
# Lemma 18.28.6

Restriction of a flat module sheaf to a slice site is flat.  The statement uses the canonical
`over` operation and inferred monoidal structures.
-/

@[expose] public section

/- Lemma 18.28.6 (0E8J): flatness is preserved by restriction to a slice. -/
@[stacks 0E8J]
#check @SheafOfModules.RingedSite.isFlat_over
