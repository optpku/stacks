/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealProjective.Annihilator
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.71.5

@stack 0G94
-/

/-!
# Lemma 15.71.5: the annihilator criterion
-/

/- Lemma 15.71.5: an ideal contained in a module's annihilator makes that module
ideal-projective. -/
@[stacks 0G94]
#check @Module.IsIdealProjective.of_le_annihilator

/- Strong ideal-valued form: the whole annihilator lies in the projective-factor ideal. -/
#check @Module.projectiveFactorIdeal.annihilator_le
