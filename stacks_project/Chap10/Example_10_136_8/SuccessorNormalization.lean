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
# Elementary-symmetric support for Example 10.136.8

The former successor and `AdjoinRoot` proof route is subsumed by the canonical
elementary-symmetric coefficient map and its finite-free theorem.

@stack 00SR
-/

/- Example 10.136.8, tag `00SR`: the `Fin n` elementary-symmetric coefficient map. -/
@[stacks 00SR "Fin-indexed elementary-symmetric coefficient map"]
#check @MvPolynomial.ElementarySymmetric.algHomFin

@[stacks 00SR "elementary-symmetric coefficient generator"]
#check @MvPolynomial.ElementarySymmetric.algHomFin_apply_X

@[stacks 00SR "finite-free elementary-symmetric extension"]
#check @MvPolynomial.ElementarySymmetric.finiteFreeFin
