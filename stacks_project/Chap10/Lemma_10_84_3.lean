/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DirectSumDevissage.Kaplansky
import StacksCheckRecall

/-!
# Lemma 10.84.3

@stack 058W
-/

@[expose] public section

/- Lemma 10.84.3 (Tag 058W): an `R`-module is an internal direct sum of countably generated
modules exactly when it admits a Kaplansky direct-sum devissage. -/
@[stacks 058W]
#check @Module.isDirectSumOfCountablyGenerated_iff_hasKaplanskyDevissage

/- The two directional APIs used to consume the equivalence without unpacking an iff. -/
@[stacks 058W "Kaplansky devissage existence"]
#check @Module.exists_kaplanskyDevissage_of_isDirectSumOfCountablyGenerated

@[stacks 058W "direct-sum criterion from Kaplansky devissage"]
#check @Module.isDirectSumOfCountablyGenerated_of_kaplanskyDevissage
