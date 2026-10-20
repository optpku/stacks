/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Extension
import StacksCheckRecall

/-!
# Lemma 15.75.9

@stack 066W

Derived base change sends a perfect complex over `A` to a perfect complex over `B`.  The explicit
ring-map statement is owned by `DerivedCategory.IsPerfect.extension`.
-/

@[expose] public section

open CategoryTheory

@[stacks 066W "Lemma 15.75.9"]
#check @DerivedCategory.IsPerfect.extension
