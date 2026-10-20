/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Tensor model support for Lemma 10.134.12

The reusable owner is the neutral `Algebra.Extension.NaiveCotangent.BaseChange`
API.  This file remains only as a chapter-local import path for the source
recall; consumers should import the ReasLib leaf directly.

@stack 08JZ
-/

open scoped TensorProduct

/- Lemma 10.134.12 [stacks 08JZ]: the literal scalar extension and its
explicit two-term tensor model are provided by the shared base-change API. -/
@[stacks 08JZ "scalar-extension model"]
#check @Algebra.Extension.NaiveCotangent.BaseChange.scalarExtension
@[stacks 08JZ "two-term tensor model"]
#check @Algebra.Extension.NaiveCotangent.BaseChange.tensorModel
@[stacks 08JZ "scalar-extension tensor normalization"]
#check @Algebra.Extension.NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
@[stacks 08JZ "scalar-extension comparison map"]
#check @Algebra.Extension.NaiveCotangent.BaseChange.toComp
