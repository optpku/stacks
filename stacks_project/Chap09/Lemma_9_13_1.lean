/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 9.13.1: pairwise distinct multiplicative characters `χ₁, …, χₙ : G → L` of a monoid
with values in a field are linearly independent. This is the finite-family specialization of the
canonical mathlib theorem `linearIndependent_monoidHom`, which states that all multiplicative
characters `G →* L` are linearly independent as functions `G → L`; applying it to an injective
family `χ : Fin n → G →* L` gives the textbook statement. -/
@[stacks 0CKL]
#check linearIndependent_monoidHom
