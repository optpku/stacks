/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Derivation.NonPthPower
import StacksCheckRecall

/-!
# Lemma 15.48.5

@stack 07PH
-/

@[expose] public section

/- Lemma 15.48.5 (07PH): a non-`p`th-power in the fraction field of a finite-type domain over a
Noetherian complete local ring is detected by an absolute derivation. -/
@[stacks 07PH "non-pth-powers detected by derivations"]
#check @Derivation.exists_apply_ne_zero_of_not_exists_pthRoot
