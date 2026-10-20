/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap104.Proposition_104_8_4_Factories
public import stacks_project.Chap104.Proposition_104_8_4_Sites
public import stacks_project.Chap104.Proposition_104_8_4_Large
public import stacks_project.Chap104.Proposition_104_8_4_Forward
public import stacks_project.Chap104.Proposition_104_8_4_Comparison

/-!
# Quasi-coherent derived objects on an algebraic stack
-/

@[expose] public section

universe u

/- Proposition 104.8.4: let `𝒳` be an algebraic stack. Then `QC(𝒳)` is
canonically equivalent to `D_QCoh(𝒪_𝒳)`. -/
@[stacks 0H16]
#check AlgebraicGeometry.AlgebraicStack.qcEquivalence
