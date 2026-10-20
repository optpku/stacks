/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.61.6 (08HX)

@stack 08HX
-/

/- Lemma 15.61.6, Stacks `08HX`: Tor independence is equivalent to its compatible prime-local
forms and to prime-local vanishing of the positive Tor modules over the tensor-product algebra. -/
@[stacks 08HX "Lemma 15.61.6, local criteria for Tor independence"]
#check @CategoryTheory.ModuleCat.Tor.IsIndependent.tfae_localization
