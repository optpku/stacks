/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ModuleExtension
import StacksCheckRecall

/-!
# Lemma 15.75.10

@stack 066X

For a flat map `A → B`, ordinary extension of scalars sends a perfect `A`-module to a perfect
`B`-module.  The explicit-map module owner is `ModuleCat.IsPerfect.extendScalars`.
-/

@[expose] public section

open CategoryTheory

@[stacks 066X "Lemma 15.75.10"]
#check @ModuleCat.IsPerfect.extendScalars
