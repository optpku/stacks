/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.FlatBaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.134.8: Flat base change

@stack 00S4

The source statement is the canonical self-presentation specialization of the
shared flat source-base-change API.
-/

/- Lemma 10.134.8 (Flat base change) [stacks 00S4]: if `T` is flat over `R`, then the literal
scalar extension of the canonical naive cotangent complex of `S` over `R` is homotopy equivalent
to the canonical naive cotangent complex of `T ⊗[R] S` over `T`. -/
@[stacks 00S4]
#check @Algebra.NaiveCotangent.FlatBaseChange.homotopyEquiv

#check @Algebra.Extension.NaiveCotangent.FlatBaseChange.homotopyEquiv
#check @Algebra.tensorH1CotangentOfFlat
