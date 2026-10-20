/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.FlatLocus
import StacksCheckRecall

/-!
# Descent with an algebra-side closed subset

Lemma 15.19.4 is the essentially finitely presented, algebra-ideal companion to the canonical
finite-stage flat-locus descent theorem.

@stack 05LT
-/

@[stacks 05LT "Lemma 15.19.4"]
#check @Ring.DirectLimit.FlatLocus.exists_stage_add

@[stacks 05LT "finite-presentation companion without the algebra ideal"]
#check @Ring.DirectLimit.FlatLocus.exists_stage
