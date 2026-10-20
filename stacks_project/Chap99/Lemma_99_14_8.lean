/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.LimitPreserving
import StacksCheckRecall

/-!
# Lemma 99.14.8

The stack in groupoids Polarized is limit preserving in the sense of
Artin's Axioms, Definition 98.11.1.
-/

@[expose] public section

universe u

/- Lemma 99.14.8: the stack in groupoids Polarized is limit preserving
(Artin's Axioms, Definition 98.11.1). -/
@[stacks 0D43]
#check (AlgebraicGeometry.Polarized.instLimitPreserving.{u} :
  AlgebraicGeometry.Groupoids.LimitPreserving
    AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ.{u})
