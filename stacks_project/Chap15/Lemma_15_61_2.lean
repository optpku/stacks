/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.TorIndependent
import StacksCheckRecall

/-!
# Tor-independent derived base change

@stack 0661
-/

@[expose] public section

/- Lemma 15.61.2: the explicit derived tensor-product pushout comparison is an isomorphism under
Tor independence. -/
@[stacks 0661 "Tor-independent derived base-change comparison"]
#check @CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct.comparisonApp_isIso_of_torIndependent

@[stacks 065Z "derived pushout comparison at an object"]
#check @CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct.comparisonApp
