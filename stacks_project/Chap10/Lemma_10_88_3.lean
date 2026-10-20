/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Domination.FinitePresentation

@[expose] public section

/-!
Chapter 10, Lemma 10.88.3 is the finite-presentation detection theorem for tensor-kernel
domination.

@stack 059C
-/

@[stacks 059C]
#check LinearMap.Dominates.iff_forall_finitePresentation
