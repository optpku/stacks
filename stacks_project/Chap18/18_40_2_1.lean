/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Equation 18.40.2.1 (05D7): the canonical map from the sheafified empty presheaf to the
equalizer of the zero and one sections. -/
@[stacks 05D7]
#check @Sheaf.nontrivialityMap
