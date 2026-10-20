/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Tensor
import StacksCheckRecall

/-!
# Lemma 15.75.11

@stack 0GM0

Perfect objects are closed under the derived tensor product.  ReasLib owns the statement at the
fixed-right `DerivedTensor.Right.obj` level.
-/

@[expose] public section

open CategoryTheory

@[stacks 0GM0 "Lemma 15.75.11"]
#check @DerivedCategory.IsPerfect.tensor
