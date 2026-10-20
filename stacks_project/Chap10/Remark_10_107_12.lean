/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.Epicenter.Matrix.Associated
import StacksCheckRecall

/-!
# Epicenters and associated matrix triples

@stack 04VZ
-/

@[expose] public section

@[stacks 04VZ "(1), epicenter"]
#check @Algebra.epicenter

@[stacks 04VZ "(1), membership"]
#check @Algebra.mem_epicenter

@[stacks 04VZ "(1), finite matrix criterion"]
#check @Algebra.Epicenter.mem_iff_hasMatrixExpr

@[stacks 04VZ "(2)"]
#check @Algebra.Epicenter.MatrixExpr.IsAssociated

@[stacks 04VZ "(3)"]
#check @Algebra.Epicenter.exists_associated
