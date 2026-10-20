/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Polynomial
import StacksCheckRecall

/-!
# Lemma 10.103.13

@stack 0AAI
-/

@[expose] public section

/-
Lemma 10.103.13 (Stacks tag `0AAI`) is a direct recall of the exact
natural-number-indexed specialization.  The reusable theorem is generalized
to arbitrary finite variable types in
`Module.LocallyCohenMacaulay.mvPolynomial`; this chapter view keeps the
source's `Fin n` presentation through its tagged bridge.
-/
@[stacks 0AAI]
#check @Module.LocallyCohenMacaulay.mvPolynomial_fin
