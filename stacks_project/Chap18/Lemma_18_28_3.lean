/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Sheafification
import StacksCheckRecall

/-!
# Lemma 18.28.3

Flatness is preserved by module sheafification.  The reusable owner is itself the canonical
typeclass instance.
-/

@[expose] public section

/- Lemma 18.28.3 (03ET): sheafification carries flat module presheaves to flat module sheaves. -/
@[stacks 03ET]
#check @PresheafOfModules.sheafification_isFlat
