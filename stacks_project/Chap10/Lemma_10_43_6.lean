/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.TensorProduct
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyReduced
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.43.6

Lemma 10.43.6 (Tag 030U) is a canonical recall of
`Algebra.IsSeparableOver.isReduced_tensorProduct`: if `K / k` is separable over
`k` in the sense of Definition 10.42.1 (2), then `K ⊗[k] S` is reduced for every
reduced `k`-algebra `S`.  The source's separately stated separably generated
alternative is absorbed by `Algebra.IsSeparablyGenerated.isSeparableOver`.
Its geometric-reducedness consequence is `Algebra.IsSeparableOver.isGeometricallyReduced`.

@stack 030U
-/

@[stacks 030U]
#check @Algebra.IsSeparableOver.isReduced_tensorProduct
#check @Algebra.IsSeparablyGenerated.isSeparableOver
#check @Algebra.IsSeparableOver.isGeometricallyReduced
