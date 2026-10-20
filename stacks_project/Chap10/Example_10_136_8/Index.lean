/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Symmetric.FiniteFree
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.136.8 support index

The reusable elementary-symmetric map and finite-free result are owned directly by `ReasLib`.

@stack 00SR
-/

@[stacks 00SR "finite-free elementary-symmetric extension"]
#check @MvPolynomial.ElementarySymmetric.finiteFreeFin
