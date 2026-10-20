/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.TensorProduct
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

/-!
# Finite and finitely presented tensor products

Lemma 10.12.14 (Tag 05BS) records two independent closure statements.  The
finite statement is provided by Mathlib, while the finitely-presented closure
is owned by `ReasLib.Algebra.Module.FinitePresentation.TensorProduct`.

@stack 05BS
-/

/- Lemma 10.12.14 (Tag 05BS) (1): tensor products of finite modules are finite. -/
@[stacks 05BS "(1)"]
#check @Module.Finite.tensorProduct

/- Lemma 10.12.14 (Tag 05BS) (2): tensor products of finitely presented modules are finitely
presented. -/
@[stacks 05BS "(2)"]
#check @Module.FinitePresentation.tensorProduct

end
