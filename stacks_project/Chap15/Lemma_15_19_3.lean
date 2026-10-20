/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Locus.Descent
import StacksCheckRecall

/-!
# Descent with a closed subset of the algebra

Lemma 15.19.3 is the source-and-base closed-subset form of tensor-product flatness descent.

@stack 05LS
-/

@[stacks 05LS "Lemma 15.19.3"]
#check @Ideal.FlatLocus.tensorBaseChange_add_descends

@[stacks 05LS "closed-subset descent without the algebra ideal"]
#check @Ideal.FlatLocus.tensorBaseChange_descends
