/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.BaseChange

/-!
# Lemma 15.61.4

@stack 0FXF

The algebra-facing specialization is owned by ReasLib together with the bundled-module theorem.
-/

@[expose] public section

/- Lemma 15.61.4: flat base change preserves Tor independence in the source tensor-product
presentation. -/
@[stacks 0FXF "flat base change for Tor-independent algebras"]
#check @CategoryTheory.ModuleCat.Tor.IsIndependent.baseChange_tensorProduct

@[stacks 0FXF "flat base change for bundled Tor independence"]
#check @CategoryTheory.ModuleCat.Tor.IsIndependent.baseChange_extendScalars
