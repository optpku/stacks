/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PID
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.125.9

@stack 0ASV

The source-shaped cyclic decomposition is a ReasLib bridge to Mathlib's stronger
prime-power structure theorem.  The chapter file records both interfaces and
contains no witness selection or quotient rewriting.
-/

/- Lemma 15.125.9: finite modules over a PID decompose into free and cyclic parts. -/
@[stacks 0ASV "Lemma 15.125.9, finite module decomposition over a PID"]
#check @Module.exists_equiv_free_prod_directSum_principalQuotients

#check @Module.equiv_free_prod_directSum
