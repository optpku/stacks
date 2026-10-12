/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
