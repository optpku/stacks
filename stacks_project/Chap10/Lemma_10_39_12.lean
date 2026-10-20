/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
import StacksCheckRecall

/-!
# Lemma 10.39.12

@stack 00HL
-/

@[expose] public section

/- Lemma 10.39.12: a short exact sequence of modules with flat cokernel remains short exact
after tensoring with any module; equivalently, it is universally exact. -/
@[stacks 00HL]
#check @CategoryTheory.ShortComplex.ShortExact.universallyExact_of_flat_X₃

@[stacks 00HL "tensor-left short exactness"]
#check @CategoryTheory.ShortComplex.ShortExact.tensorLeft_shortExact_of_flat_X₃
