/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.PerfectField
import StacksCheckRecall

@[expose] public section

/-!
# Reduced Algebras Over Perfect Fields

Lemma 10.45.6 is a canonical recall of the field-theoretic geometric-reducedness
bridge and its tensor-product application.

@stack 00I4
-/

/- Lemma 10.45.6 (Tag 00I4): over a perfect field, reduced commutative algebras are
geometrically reduced, and hence two reduced algebras have reduced tensor product. -/
@[stacks 00I4]
#check @Algebra.IsGeometricallyReduced.of_perfectField

@[stacks 00I4 "perfect-field tensor-product reducedness"]
#check @Algebra.TensorProduct.isReduced_of_perfectField
